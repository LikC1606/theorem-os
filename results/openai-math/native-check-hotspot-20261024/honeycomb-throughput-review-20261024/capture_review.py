#!/usr/bin/python3
"""Snapshot public run metadata; never inspect model reasoning or solution files."""
import hashlib
import json
import statistics
from datetime import datetime, timezone
from pathlib import Path

C = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022')
OUT = Path(__file__).resolve().parent
RUN_ID = '8bd4a613-c70e-4e96-b298-c9d22cfafaf3'
EDIT_ID = 'honeycomb-lead-reuse-advisory-20261024'
REFERENCE_ID = 'finite_box_zero_mass_reference'
STATE = C / 'tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime/state.json'
LOG = C / 'tasks/HoneycombBridgeFiniteness/solve.log'


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def utc(at):
    return datetime.fromtimestamp(at / 1000, timezone.utc).isoformat()


def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


raw_log = LOG.read_bytes()
events = []
total_lines = 0
for number, line in enumerate(raw_log.splitlines(), 1):
    total_lines = number
    try:
        event = json.loads(line)
    except (ValueError, TypeError):
        continue
    if isinstance(event, dict) and event.get('runId') == RUN_ID:
        events.append((number, event))

state = json.loads(STATE.read_text())
assert state['runId'] == RUN_ID
cooperation = state['cooperation']
before = json.loads((OUT / 'state-before.json').read_text())
plan = json.loads((OUT / 'advisory-plan.json').read_text())
advisory = (OUT / 'ADVISORY.txt').read_text().strip()
edit = next(edit for edit in cooperation['edits'] if edit['id'] == EDIT_ID)
assert edit['status'] == 'applied'
assert edit['affectedTasks'] == [REFERENCE_ID]
assert edit['recheck'] == {'status': 'not-required', 'tasks': []}
at = edit['appliedAt']
cutoff = max(event['at'] for _, event in events if isinstance(event.get('at'), (int, float)))
captured = datetime.now(timezone.utc).isoformat()

after_tasks = [{
    'task': node['task'], 'definitionDigest': digest(node['task']),
    'status': node['status'], 'assignment': node.get('assignment'),
    'attempts': node.get('attempts'), 'alternativeRoutes': node.get('alternativeRoutes'),
} for node in cooperation['tasks']]
after = {
    'capturedAt': captured, 'stateFile': str(STATE), 'runId': RUN_ID,
    'phase': state['phase'], 'planVersion': cooperation['planVersion'],
    'canonicalCommit': cooperation.get('canonicalCommit'), 'tasks': after_tasks,
    'groups': cooperation.get('groups'),
    'proofRoutesPresent': 'proofRoutes' in cooperation,
    'proofRoutes': cooperation.get('proofRoutes'),
    'workers': [{'id': worker.get('id'), 'role': worker.get('role'),
                 'turns': worker.get('turns'), 'scheduling': worker.get('scheduling'),
                 'worktree': worker.get('worktree')} for worker in state['workers']],
}
save('state-after.json', after)
old = {node['task']['id']: node for node in before['tasks']}
new = {node['task']['id']: node for node in after_tasks}
changed = [task_id for task_id in old if old[task_id]['task'] != new[task_id]['task']]
assignments_equal = {task_id: old[task_id]['assignment'] == new[task_id]['assignment'] for task_id in old}
assert set(old) == set(new) and changed == [REFERENCE_ID]
assert all(assignments_equal.values())
assert new[REFERENCE_ID]['task']['objective'] == old[REFERENCE_ID]['task']['objective'] + '\n\n' + advisory + '\n'
assert new[REFERENCE_ID]['status'] == 'pending' and not new[REFERENCE_ID]['assignment']
assert new[REFERENCE_ID]['attempts'] == 0
group_definitions_equal = [g['group'] for g in before['groups']] == [g['group'] for g in after['groups']]
assert group_definitions_equal and (before['proofRoutes'] or []) == (after['proofRoutes'] or [])
invariants = {
    'sameTaskIds': True, 'changedTaskDefinitions': changed,
    'allExistingAssignmentsEqual': assignments_equal,
    'allOtherTaskDefinitionsEqual': True, 'referenceObjectiveAppendOnly': True,
    'referenceStillUnassigned': True, 'referenceAttempts': new[REFERENCE_ID]['attempts'],
    'groupDefinitionsEqual': group_definitions_equal,
    'groupCounters': {'before': before['groups'], 'after': after['groups'],
                      'note': 'busy and turns are live runtime counters, not plan definitions'},
    'proofRoutesEqualAsPlan': True,
    'taskDefinitionDigestsAfter': {task_id: node['definitionDigest'] for task_id, node in new.items()},
    'assignmentTaskDigestsAfter': {task_id: (node['assignment'] or {}).get('taskDigest') for task_id, node in new.items()},
}
save('invariants.json', invariants)

# Persist only public event metadata; command bodies and model item bodies are excluded.
allowed_events = {
    'turn_started', 'turn_checkpoint', 'cooperative_checkpoint_scheduled',
    'cooperative_checkpoint_saved', 'cooperative_checkpoint_requested',
    'cooperative_checkpoint_interrupted', 'cooperative_checkpoint_deferred',
    'lead_checkpoint_saved', 'worker_activity', 'context_compiled', 'context_dispatched',
    'context_restarted', 'assignment_superseded', 'lead_decision_superseded',
    'edit_received', 'edit_applied', 'edit_rejected', 'edit_recheck_updated',
    'notification_deferred', 'task_checked', 'task_integrated', 'delivery_published',
    'plan_updated',
}
allowed_keys = {
    'event', 'at', 'workerId', 'taskId', 'turn', 'turnId', 'totalTurns', 'commit',
    'seedCommit', 'reason', 'progress', 'noProgressStreak', 'checkpointAfterMs',
    'noticeAfterMs', 'protected', 'backoffCapped', 'activity', 'itemType',
    'contentDigest', 'compiledContentDigest', 'messageDigest', 'messageBytes', 'mode',
    'requiredTaskIds', 'included', 'omitted', 'usedBytes', 'mandatoryBytes',
    'optionalBytes', 'maxOptionalBytes', 'maxBytes', 'id', 'editId', 'baseVersion',
    'planVersion', 'affectedTasks', 'recheck', 'invalidated', 'status', 'runId',
}
metadata = [{'line': line, **{key: value for key, value in event.items() if key in allowed_keys}}
            for line, event in events if event.get('event') in allowed_events]
(OUT / 'events-metadata.jsonl').write_text(''.join(json.dumps(item, ensure_ascii=False) + '\n' for item in metadata))
save('capture.json', {
    'capturedAt': captured, 'runId': RUN_ID, 'sourceLog': str(LOG),
    'sourceBytes': len(raw_log), 'sourceTotalLines': total_lines,
    'sourceSnapshotSha256': hashlib.sha256(raw_log).hexdigest(),
    'firstMatchingLine': events[0][0], 'lastMatchingLine': events[-1][0],
    'cutoffAt': cutoff, 'cutoffUtc': utc(cutoff), 'persistedEvents': len(metadata),
    'eventPolicy': 'Exact top-level runId match; whitelisted public metadata only; no command or reasoning bodies',
})

lead_starts = [(line, event) for line, event in events if event.get('event') == 'turn_started'
               and event.get('workerId') == 'solver']
rows = []
for index, (line, event) in enumerate(lead_starts):
    if not 88 <= event['turn'] <= 107:
        continue
    end = lead_starts[index + 1][1]['at'] if index + 1 < len(lead_starts) else cutoff + 1
    window = [(n, item) for n, item in events if event['at'] <= item.get('at', -1) < end]
    saved = [(n, item) for n, item in window if item.get('event') == 'cooperative_checkpoint_saved'
             and item.get('workerId') == 'solver']
    checkpoints = [(n, item) for n, item in window if item.get('event') == 'lead_checkpoint_saved']
    rows.append({
        'turn': event['turn'], 'startLine': line, 'startAt': event['at'], 'startUtc': utc(event['at']),
        'nextStartDeltaSeconds': (end - event['at']) / 1000,
        'commandExecutionsCompleted': sum(item.get('event') == 'worker_activity'
            and item.get('workerId') == 'solver' and item.get('activity') == 'item_completed'
            and item.get('itemType') == 'commandExecution' for _, item in window),
        'checkpointSaved': [{'line': n, **{key: item[key] for key in ['at', 'progress', 'noProgressStreak'] if key in item}}
                            for n, item in saved],
        'checkpointCommits': [{'line': n, 'commit': item.get('commit')} for n, item in checkpoints],
        'planUpdates': sum(item.get('event') == 'plan_updated' for _, item in window),
        'publishedDeliveries': sum(item.get('event') == 'delivery_published' for _, item in window),
    })
core_rows = [row for row in rows if row['turn'] <= 102]
save('lead-rounds.json', {
    'turns': rows,
    'turn88to102': {
        'medianStartIntervalSeconds': statistics.median(row['nextStartDeltaSeconds'] for row in core_rows),
        'completedCommands': sum(row['commandExecutionsCompleted'] for row in core_rows),
        'planUpdates': sum(row['planUpdates'] for row in core_rows),
        'publishedDeliveries': sum(row['publishedDeliveries'] for row in core_rows),
        'checkpointCommits': sorted({item['commit'] for row in core_rows for item in row['checkpointCommits']}),
        'lastCheckpoint': core_rows[-1]['checkpointSaved'],
    },
    'limits': [
        'Completed command events do not reveal command bodies or mathematical value.',
        'Context included/omitted fields are counts, not hashes or evidence-set identities.',
        'Different content/message digests preclude claiming byte-identical contexts.',
    ],
})

activity = []
for worker in state['workers']:
    worker_id = worker['id']
    commands = [(line, event) for line, event in events if event.get('event') == 'worker_activity'
                and event.get('workerId') == worker_id and event.get('activity') == 'item_completed'
                and event.get('itemType') == 'commandExecution' and event.get('at', 0) <= at]
    recent = [(line, event) for line, event in commands if event['at'] >= at - 30 * 60 * 1000]
    activity.append({
        'workerId': worker_id, 'role': worker['role'],
        'currentScheduling': worker.get('scheduling'),
        'completedCommands30mBeforeEdit': len(recent),
        'completedCommands15mBeforeEdit': sum(event['at'] >= at - 15 * 60 * 1000 for _, event in recent),
        'lastCommandBeforeEdit': {'line': commands[-1][0], 'at': commands[-1][1]['at'],
                                  'utc': utc(commands[-1][1]['at'])} if commands else None,
    })
save('worker-activity.json', {'windowEndAt': at, 'windowEndUtc': utc(at), 'workers': activity,
                            'limit': 'Tool activity alone does not establish useful new mathematics.'})

lead = next(worker for worker in state['workers'] if worker['id'] == 'solver')
lead_worktree = Path(lead['worktree'])
manifest_file = lead_worktree / 'CONTEXT-MANIFEST.json'
manifest = json.loads(manifest_file.read_text())
cooperation_file = lead_worktree / 'COOPERATION.json'
lead_cooperation = json.loads(cooperation_file.read_text())


def matches(value, pointer=''):
    result = []
    if isinstance(value, str) and advisory in value:
        result.append({'jsonPointer': pointer, 'stringSha256': hashlib.sha256(value.encode()).hexdigest(),
                       'bytes': len(value.encode()), 'advisoryExactTextPresent': True})
    elif isinstance(value, dict):
        for key, item in value.items():
            result.extend(matches(item, pointer + '/' + str(key).replace('~', '~0').replace('/', '~1')))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            result.extend(matches(item, pointer + '/' + str(index)))
    return result


advisory_matches = matches(lead_cooperation)
assert advisory_matches and lead_cooperation['planVersion'] == edit['planVersion']
assert REFERENCE_ID in manifest['requiredTaskIds']
compiled = [(line, event) for line, event in events if event.get('event') == 'context_compiled'
            and event.get('workerId') == 'solver' and event.get('contentDigest') == manifest['contentDigest']
            and event['at'] >= at]
dispatched = [(line, event) for line, event in events if event.get('event') == 'context_dispatched'
              and event.get('workerId') == 'solver' and event.get('compiledContentDigest') == manifest['contentDigest']
              and event['at'] >= at]
assert compiled and dispatched
save('lead-context-manifest.json', manifest)
visibility = {
    'planVersion': lead_cooperation['planVersion'], 'cooperationFile': str(cooperation_file),
    'cooperationMtimeNs': cooperation_file.stat().st_mtime_ns,
    'advisoryMatches': advisory_matches,
    'manifestFile': str(manifest_file), 'manifestContentDigest': manifest['contentDigest'],
    'referenceInRequiredTaskIds': True,
    'compiledEventLines': [line for line, _ in compiled],
    'dispatchedEventLines': [line for line, _ in dispatched],
    'scope': 'Advice is available through the lead shared context/reference; this does not prove model attention or adoption.',
}
save('lead-visibility.json', visibility)

after_edit = [(line, event) for line, event in events if event.get('at', 0) >= at]
superseded = [{'line': line, 'workerId': event.get('workerId'), 'event': event['event']}
              for line, event in after_edit if event.get('event') in ['assignment_superseded', 'lead_decision_superseded']]
integrations = [(line, event) for line, event in events if event.get('event') == 'task_integrated']
integration_pairs = []
for line, event in integrations:
    checked = [(n, item) for n, item in events if item.get('event') == 'task_checked'
               and item.get('taskId') == event.get('taskId') and item.get('at', 0) <= event['at']]
    integration_pairs.append({'taskId': event.get('taskId'), 'checkedLine': checked[-1][0] if checked else None,
                              'integratedLine': line, 'checkedToIntegratedSeconds':
                              (event['at'] - checked[-1][1]['at']) / 1000 if checked else None,
                              'commit': event.get('commit')})
save('build-switch-evidence.json', {
    'runId': RUN_ID, 'integrationCount': len(integrations), 'integrations': integration_pairs,
    'decision': 'Keep the active build and long mathematical investigations.',
    'basis': 'The validated cache patch saves future same-run/same-projection rechecks; current-run repeated integrations are too rare to justify migration and restoration costs.',
    'boundary': 'No build switch, runtime code modification, or migration was performed; the cache patch does not address the 120-second lead checkpoint policy.',
})
result = {
    'schema': 'honeycomb-throughput-review.v1', 'capturedAt': captured, 'runId': RUN_ID,
    'cutoffLine': events[-1][0], 'cutoffUtc': utc(cutoff), 'edit': edit,
    'delivery': {'queued': True, 'applied': True, 'leadContextAvailable': True,
                 'actualAdoption': 'not-established', 'performanceEffect': 'not-measured'},
    'invariants': {'onlySharedReferenceChanged': True, 'existingAssignmentsPreserved': True,
                   'groupDefinitionsPreserved': True, 'proofRoutesPreserved': True,
                   'referenceRemainedUnassigned': True},
    'nativeProtocolEffects': {'supersededEventsAfterEdit': superseded,
        'note': 'A new plan version superseded the previous lead decision and restarted its context; no mathematical task assignment was invalidated by this edit.'},
    'postEditObservationSeconds': max(0, cutoff - at) / 1000,
    'mainTheoremAcceptance': 'not-established',
    'buildDecision': 'retain-current-build',
}
save('result.json', result)
print(json.dumps({'result': result, 'workerActivity': activity,
                  'lead88to102': json.loads((OUT / 'lead-rounds.json').read_text())['turn88to102'],
                  'integrationPairs': integration_pairs}, ensure_ascii=False, indent=2))

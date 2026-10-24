# CharacterVarieties 全目标最终验收归档

CharacterVarietiesAllSeamsSupport 已完成 TheoremOS 原生最终验收：result 的 status/run_outcome 均为 `evaluated_passed`，state.phase=`finished`。终态事件为原 `resume.log` 第 351 行，时间 2026-10-24T12:26:55.298000+00:00（北京时间 2026-10-24 20:26:55）。本包冻结于 2026-10-24T12:49:58.715680+00:00，只读保存所选原始文件和明确标记的提取物。

固定 evaluator 在本地调用原官方 comparator，exitCode=0、timedOut=false、aborted=false；保存的 stdout 含以下原句：

```text
Lean default kernel accepts the solution
Your solution is okay!
```

这是本地运行原官方 comparator 的验收记录，尚无 OpenAI 托管认证。runtime 记录 `method=external-command`、`official=false`，本包保持该字段原样。原配置仅将模块名改为 `Challenge`/`Submission`，theorem_names、definition_names、三标准 permitted_axioms 与 enable_nanoda=false 均不变。comparator 二进制 SHA 与既有 tools manifest 一致：`104ea0297ecd090486b15eb8f2be590318eb58ccd552c2779b22f64c318070f1`，工具 commit `71b52ec29e06d4b7d882726553b1ceb99a2499e0`。

原目标为 `OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams`，声明 hash `fb95bc071af2179a40770979bb7e3eb978b53a19ec0691d8eaf4e38a4e3d50d8`。官方来源 `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`；Challenge SHA256 `ebc3129bfb5ef4a47e0de1d89f0f406ef6603df32355bdfbb9ce278627c1a1f1`。接受的 solution commit `df8db6c4f2f872ff9c5d4a79a5c874d4707b48c0`，Submission.lean 为 795645 字节，SHA256 `5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3`。commit 在 result、state check、verification receipt、canonical/review 和最终 candidate_selected 事件一致；文件 SHA 与 receipt proofHash、交付准备记录及最终 workspace 文件一致。aggregateCheckSourceDigest 是组合源码身份，不能当作单文件 SHA。

原生 Lean receipt `lean-7af748514c728f28377b0d13` 为 kernel_verified，kernel exitCode=0；goalsRemaining/sorryCount/admitCount 均为 0；公理精确为 `propext`、`Classical.choice`、`Quot.sound`。原始声明 hash 与冻结目标一致，固定复审为 accepted。state.candidate.status 保留了早期 failed 字段，但最终 check、复审、固定 evaluator 和终态记录均通过；本包未修改原始 state，也不以该中间字段替代终态。

现有五项通过 audit 加本题后，原生最终通过总数为 **6**：TruffetCounterexample、SurfaceConeCandidateSupport、HadamardCubeFiber、CartierChartCompactnessSupport、SnakyCertificate、CharacterVarietiesAllSeamsSupport。前五项回执按原字节归档到 prior-five/。**SnakyConditional 普通 35 步任务尚未完成最终验收**，它与已通过的 SnakyCertificate 分开计数。旧 campaign-state/results.csv 尚未汇入所有补跑结果，本包不修改这些历史记录或 results 仓库。

现存输出有明确边界：raw/result.json、raw/state.json、raw/startup.log、raw/resume.log 以及其它 raw-file-copy 项均保留完整原始字节；原始事件日志的 worker_activity 只有 itemType 等元数据，没有模型隐藏推理正文。`events/acceptance.raw-lines.jsonl` 直接选取原始日志完整事件行，保留原行字节，索引记录原行号。`native-verification/` 是 state 已保存的完整 batch/receipt 对象提取物，stdout/stderr-preview 名称保留 preview 语义。

固定 evaluator 的原 stdout 全流没有持久化：runtime 的 `mathProcess.ts` 仅保存 12,000 字节尾部，并另算整个流的 SHA256。`fixed-evaluator/stdout-captured.txt` 逐字保留 result 已存的这段尾部，无额外换行，SHA256 `cbc05d0f19adb51e19be9d24216c4adf25fbb17e5deca3e67d7343eeb87ae747`；记录的全流 SHA256 为 `c90d164920a24b4128a53d12388464a5b9fca55f27824cb7d4ec72d8416a74b2`，二者有意分开，不能声称已保有完整 stdout。stderr 完整且为空。implementation/ 保存相关输出捕获代码的原文件。未用新运行填补缺失输出。

`fixed-evaluator/command.sh` 与 comparator.runtime-config.json 从原 launch 参数及 heredoc 精确提取，后者是已被正常清理的临时配置的文本重建，不冒充保存下来的临时文件。`raw/launch.json` 和原 official config 均保留，可复查唯一两项模块适配。

本次没有新 Lean/comparator/模型调用，没有改活动源码、缓存、runtime/state、队列或已有成果包，没有 Git 操作。没有归档模型 session、隐藏 reasoning、ProducedSolution 文件内容、含 capability token 的环境描述符或凭据。

主要文件：

- raw/：最终 result/state、原始 startup/resume 事件、launch、任务、active-problem 和准备/工具身份。
- accepted-source/：最终 Submission、原 Challenge 和固定 Lean/Lake 配置。
- official/：原官方 Challenge/config 及目标映射条目。
- native-verification/、fixed-evaluator/、events/：明确标记来源和截断边界的提取物。
- prior-five/：此前五项通过回执及 SnakyCertificate 终态 manifest。
- verification.json：目标、commit/SHA、公理、exit、输出边界与计数核对结论。
- archive-origins.json：逐文件区分原始复制与字段/事件提取，给出精确来源。
- manifest.json：全部 payload 的相对/绝对路径、字节数与 SHA256；SHA256SUMS 另校验 manifest 自身，不循环校验。

校验命令：

```sh
cd /home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/character-native-final-20261024
sha256sum -c SHA256SUMS
```

import { describe, expect, it } from 'vitest';
import { assertWebContainerBoundary, assertWebEnvironmentReport } from '../scripts/test-web-runtime';
import { getLeanTaskEnvironment } from '../src/math/leanTaskEnvironment';

const fixture = (environment: 'standard' | 'mathlib' = 'standard') => [{ State: { Running: true }, Config: { User: '10001:10001', Env: ['PATH=/usr/bin'],
  Cmd: null as string[] | null, Entrypoint: ['bun', 'apps/web/worker.ts'] },
  HostConfig: { ReadonlyRootfs: true, CapDrop: ['ALL'], Privileged: false, Memory: (environment === 'mathlib' ? 8 : 4) * 1024 ** 3,
    MemorySwap: (environment === 'mathlib' ? 8 : 4) * 1024 ** 3, PidsLimit: 256, NanoCpus: 2e9, SecurityOpt: ['no-new-privileges'],
    Binds: null, Tmpfs: { '/work': 'rw', '/tmp': 'rw' }, MaskedPaths: [] as string[],
    ReadonlyPaths: [] as string[], PidMode: '', Devices: environment === 'mathlib' ? [{ PathOnHost: '/dev/fuse', PathInContainer: '/dev/fuse', CgroupPermissions: 'rw' }] : [] },
  Mounts: (environment === 'mathlib' ? [{ Type: 'volume', Name: 'a'.repeat(64), Driver: 'local', RW: true, Source: '/docker/volumes/fixture', Destination: '/var/tmp' }] : []) as
    { Type: string; Name?: string; Driver?: string; RW?: boolean; Source: string; Destination: string }[] }];

describe('offline web runtime container inspection assertions', () => {
  const key = 'sk-theoremos-smoke-test-only';
  it('accepts an isolated unprivileged worker without credential metadata', () => {
    expect(() => assertWebContainerBoundary(JSON.stringify(fixture()), key)).not.toThrow();
  });
  it.each(['Env', 'Cmd', 'Entrypoint'] as const)('rejects a credential in Config.%s', field => {
    const metadata = fixture();
    metadata[0].Config[field] = [key];
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key)).toThrow('metadata must not contain');
  });
  it('checks credential absence across the entire Docker inspection result', () => {
    const metadata = { ...fixture()[0], arbitraryField: { credential: key } };
    expect(() => assertWebContainerBoundary(JSON.stringify([metadata]), key)).toThrow('metadata must not contain');
  });
  it.each(['ReadonlyRootfs', 'CapDrop', 'Memory', 'PidsLimit', 'Privileged', 'SecurityOpt'] as const)('rejects missing or relaxed %s', field => {
    const metadata = fixture();
    const weakened = { ReadonlyRootfs: false, CapDrop: [], Memory: 0, PidsLimit: 0, Privileged: true, SecurityOpt: [] };
    Object.assign(metadata[0].HostConfig, { [field]: weakened[field] });
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key)).toThrow();
  });
  it('rejects host bind mounts including a Docker socket', () => {
    const metadata = fixture();
    metadata[0].Mounts.push({ Type: 'bind', Source: '/var/run/docker.sock', Destination: '/var/run/docker.sock' });
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key)).toThrow('must not contain host binds');
  });
  it.each(['MaskedPaths', 'ReadonlyPaths'] as const)('rejects nonempty %s that would break nested sandbox mounts', field => {
    const metadata = fixture();
    metadata[0].HostConfig[field].push('/proc/sys');
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key)).toThrow('system paths');
  });
  it('rejects sharing the host process namespace', () => {
    const metadata = fixture();
    metadata[0].HostConfig.PidMode = 'host';
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key)).toThrow('isolated process namespace');
  });
  it('rejects unrelated devices or device-creation permissions', () => {
    const metadata = fixture('mathlib');
    metadata[0].HostConfig.Devices[0].PathOnHost = '/dev/sda';
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key, 'mathlib')).toThrow('unrelated host devices');
    metadata[0].HostConfig.Devices[0].PathOnHost = '/dev/fuse';
    metadata[0].HostConfig.Devices[0].CgroupPermissions = 'rwm';
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key, 'mathlib')).toThrow('must not grant device creation');
  });
  it('returns only the worker anonymous verification volume name for cleanup verification', () => {
    expect(assertWebContainerBoundary(JSON.stringify(fixture('mathlib')), key, 'mathlib')).toEqual(['a'.repeat(64)]);
    const metadata = fixture('mathlib');
    metadata[0].Mounts[0].Destination = '/var/run/docker.sock';
    expect(() => assertWebContainerBoundary(JSON.stringify(metadata), key, 'mathlib')).toThrow();
  });
  it('requires reports to bind the exact pinned Mathlib environment', () => {
    const trusted = getLeanTaskEnvironment('mathlib');
    const report = { environment: { id: trusted.id, toolchain: trusted.toolchain, dependencyDigest: trusted.dependencyDigest,
      mathlibRevision: trusted.mathlibRevision } };
    expect(() => assertWebEnvironmentReport(report, 'mathlib')).not.toThrow();
    report.environment.mathlibRevision = 'b'.repeat(40);
    expect(() => assertWebEnvironmentReport(report, 'mathlib')).toThrow('exact trusted dependency environment');
  });
});

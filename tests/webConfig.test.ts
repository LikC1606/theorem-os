import { describe, expect, it } from 'vitest';
import { readWebConfig } from '../apps/web/config';

const configure = (baseUrl: string) => readWebConfig({ THEOREMOS_WEB_PROVIDERS: JSON.stringify([
  { id: 'custom', name: 'Custom gateway', baseUrl },
]) });

describe('web provider deployment addresses', () => {
  it('accepts a host gateway reached by Docker workers and normalizes its trailing slash', () => {
    expect(configure('http://host.docker.internal:8080/v1/').providers[0].baseUrl)
      .toBe('http://host.docker.internal:8080/v1');
  });

  it('preserves configured HTTPS providers', () => {
    expect(configure('https://api.example.com/v1').providers[0].baseUrl).toBe('https://api.example.com/v1');
  });

  it.each([
    'http://api.example.com/v1', 'http://host.docker.internal.example.com:8080/v1',
    'http://host.docker.internal:8080/v1?key=private', 'http://host.docker.internal:8080/v1#private',
    'http://user:private@host.docker.internal:8080/v1', 'ftp://host.docker.internal:8080/v1',
  ])('rejects unsupported or credential-bearing provider addresses (%s)', baseUrl => {
    expect(() => configure(baseUrl)).toThrow('Provider base URLs');
  });
});

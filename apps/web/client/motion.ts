import { gsap } from 'gsap';

type MotionKind = 'workspace' | 'message' | 'event' | 'panel' | 'status' | 'dialog';
const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
const active = new Map<HTMLElement, gsap.Context>();
let pageActive = true;

function finish(target: HTMLElement) {
  const context = active.get(target);
  active.delete(target);
  context?.revert();
  delete target.dataset.motion;
}

export function finishMotion(root?: Element) {
  for (const target of active.keys()) if (!root || root === target || root.contains(target)) finish(target);
}

export function finishHiddenMotion() {
  for (const target of active.keys()) if (!target.isConnected || !target.getClientRects().length) finish(target);
}

export function animateEntrance(target: HTMLElement, kind: MotionKind) {
  finish(target);
  if (!pageActive || document.hidden || reducedMotion.matches || !target.getClientRects().length) return;
  const stationary = kind === 'workspace' || kind === 'dialog' || kind === 'status';
  target.dataset.motion = kind;
  // Revert the context on completion as well as interruption so original inline styles survive.
  const context = gsap.context(() => {
    gsap.fromTo(target, { opacity: kind === 'status' ? .55 : .35, y: stationary ? 0 : 5 }, {
      opacity: 1, y: 0, duration: kind === 'message' ? .24 : .18, ease: 'power2.out',
      onComplete: () => finish(target),
    });
  });
  active.set(target, context);
}

reducedMotion.addEventListener('change', () => finishMotion());
document.addEventListener('visibilitychange', () => { if (document.hidden) finishMotion(); });
window.addEventListener('pagehide', () => { pageActive = false; finishMotion(); });
window.addEventListener('pageshow', () => { pageActive = true; });

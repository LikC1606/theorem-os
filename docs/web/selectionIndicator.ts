import { gsap } from 'gsap';

// React Bits' GooeyNav informed the measured active target, font-ready refresh,
// and ResizeObserver lifecycle. This DOM implementation uses GSAP transforms.
// Reference: https://reactbits.dev/components/gooey-nav
export function createSelectionIndicator(list: HTMLElement, reducedMotion: MediaQueryList) {
  const tabs = Array.from(list.querySelectorAll<HTMLElement>('[role="tab"]'));
  const indicator = document.createElement('span');
  indicator.className = 'selection-indicator';
  indicator.setAttribute('aria-hidden', 'true');
  list.prepend(indicator);
  let disposed = false;
  let destination: { x: number; y: number; scaleX: number; scaleY: number } | undefined;

  function update(animate = true) {
    if (disposed) return;
    const active = tabs.find(tab => tab.getAttribute('aria-selected') === 'true');
    if (!active) return;
    // Layout offsets stay correct while the entrance animation transforms a tab.
    // The positioned list is each tab's offset parent.
    if (!active.offsetWidth || !active.offsetHeight) return;
    const next = {
      x: active.offsetLeft,
      y: active.offsetTop,
      scaleX: active.offsetWidth,
      scaleY: active.offsetHeight,
    };
    const changed = !destination || (Object.keys(next) as (keyof typeof next)[])
      .some(key => Math.abs(next[key] - destination![key]) > .1);
    if (!changed && animate) return;
    if (!destination || !animate || reducedMotion.matches || document.hidden) {
      gsap.killTweensOf(indicator);
      gsap.set(indicator, next);
    } else {
      gsap.to(indicator, { ...next, duration: .36, ease: 'power3.out', overwrite: true });
    }
    destination = next;
    list.classList.add('has-selection-indicator');
  }

  // Snap after reflow; resizing should never animate through the wrong grid cell.
  const refresh = () => update(false);
  const resize = new ResizeObserver(refresh);
  resize.observe(list);
  tabs.forEach(tab => resize.observe(tab));
  reducedMotion.addEventListener('change', refresh);
  void document.fonts.ready.then(refresh);
  update(false);

  return {
    update,
    destroy() {
      disposed = true;
      resize.disconnect();
      reducedMotion.removeEventListener('change', refresh);
      gsap.killTweensOf(indicator);
      indicator.remove();
      list.classList.remove('has-selection-indicator');
    },
  };
}

set confirm off
set pagination off
set debuginfod enabled off
set auto-solib-add off
set auto-load off
set sysroot /
file /home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
add-symbol-file /home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean/libleanshared.so -o 0x7ab2cc800000
add-symbol-file /usr/lib/x86_64-linux-gnu/libc.so.6 -o 0x7ab2cc400000
source /home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-integration-cost-20261024/capture-symbolized-stack.py
quit

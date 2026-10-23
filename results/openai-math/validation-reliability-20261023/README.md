# 验收可靠性修复

工程修复已在独立工作区实现并验证；本目录归档补丁和验证回执。运行中的冻结 runtime 未替换，补丁尚未合入运行时源码。本次归档不增加数学题通过数：完整原题模块化证明仍为 7 个，TheoremOS 原生最终通过仍为 4 个；尚无 OpenAI 托管验收确认。

- host edit 写入和读取统一使用 1 MiB UTF-8 行限制，包含规范化 JSON 最后换行；普通 worker delivery 保留 64,000 字节。dry-run 与正式入队行为一致。
- 宿主和比较器摘要保留首个 Lean 错误及上下文；被动监听输出，保留原进程生命周期、超时和沙箱行为。
- 宿主与模型预检使用 `-j1 -DElab.async=false`，参数纳入缓存身份。冻结原比较器、目标与最终验收条件保持原样。
- CharacterVarieties 外部续接使用 xz/lzma + base64，从 `COOPERATION.json` 对应任务完整 objective 读取载荷，入队前核对规范化消息长度和 SHA。

验证结果：16 个去重测试文件，344 项通过；TypeScript 检查和三个 headless bundle 构建通过；Lean 4.34.1 在原 32 GiB 地址空间限制、无超时条件下接受有效证明、拒绝错误证明。V4 候选 751,283 字节，传输消息 45,182 字节，旧冻结 reader 与沙箱解压 SHA 回环均通过。V3 只作为传输夹具，不能解释为数学成功。

运行时补丁是 `runtime-reliability-fixes.patch`，相对于仓库提交 `b580d5a8fb4a4c8373c93befbebc2af05c049f25`。外部续接脚本补丁是 `character-continuation-transport.patch`，相对于该运行目录此前的续接脚本，不修改冻结 runtime。完整源文件 SHA、补丁 SHA 和测试说明见 `validation.json`；归档文件 SHA 见 `manifest.json`。构建清单 `source.commit` 来自 `extraction.json` 的原始提取来源；工作区 Git 基线以上述提交及验证记录为准，实际构建输入逐文件列于清单中。

归档时，两道 Snaky 新候选正在跑完整原比较器，CharacterVarieties V4 正在做默认 CLI 集成检查；三题均未新增原生最终通过。新候选包含外部辅助，后续仍须经过同 SHA 的原源码保护、完整内核、独立比较器和原生最终验收。五项求解预算保持 0，不设置预算上限。

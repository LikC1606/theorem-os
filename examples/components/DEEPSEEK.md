# 使用 DeepSeek 做模块实验

本机已有 Westlake 凭据，当前实验采用 [Westlake DeepSeek 配置](WESTLAKE.md)，
选择 `--provider westlake --model deepseek-flash --effort high`。

以下说明独立的 DeepSeek 官方 API 路由，默认 `deepseek-v4-pro` / `high`。
DeepSeek 官方已支持 Responses API，可以复用现有 Codex Agent 工具和 Lean 验收流程，
无需增加 Chat Completions 转换代理。当前只完成准备和离线验证，不启动真实推理。

## 准备

按[模块实验](EXPERIMENTS.md#准备方案)构建并准备题目，在 `compare --phase prepare` 中指定：

```text
--provider deepseek --model deepseek-v4-pro --effort high
```

`--provider deepseek` 默认选择上述模型和推理强度。也可显式选择 `deepseek-flash`；
支持的推理强度为 `low`、`high`、`max`。为避免模型映射造成混淆，不使用 `xhigh` 别名。
四个方案使用同一模型、同一推理强度、同一预算和固定的独立原题验收。

`prepare` 不需要 API Key，也不调用模型。它为每次尝试创建私有的 `codex` 目录：

| 文件 | 内容 |
| --- | --- |
| `config.toml` | 官方端点 `https://api.deepseek.com`、Responses 协议、模型和密钥环境变量名 |
| `models.json` | DeepSeek 模型的上下文窗口、工具格式和推理强度元数据 |

两个文件均只读，其内容摘要写入 `comparison.json`。运行前检查配置和启动参数；
修改端点、模型目录或 profile 身份会拒绝启动。每组拥有独立的 profile 和会话记录，
不会改动用户原有 Codex 配置。运行记录绑定 profile 路径与摘要，恢复时也检查；
更换服务商后不能继续原实验。报告记录已选择的服务商，不把配置准备称为真实服务验证。

## 密钥

真正运行时，在启动实验的进程环境中设置 `DEEPSEEK_API_KEY`。
例如在 Bash 中交互输入，避免把密钥文字写进命令历史：

```bash
read -rsp 'DeepSeek API Key: ' DEEPSEEK_API_KEY
export DEEPSEEK_API_KEY
```

密钥仅注入 provider 进程，并从 Agent 的工具子进程环境中排除。
不要将其写入数学环境文件；该文件只保存可投影给求解器的工具设置。
没有密钥时，创建模型会话前即报告认证配置缺失；不会回退到 OpenAI 或其他服务商。
已有实验目录的 `--phase report` 只读取保存的证据，不需要密钥或模型请求。

## 已有 Westlake 密钥

Westlake 使用 `WESTLAKEHPC_API_KEY`，网关为 `https://hpc-api.westlake.edu.cn/v1`。
它与上面的 DeepSeek 官方服务是不同的认证入口，不应将 Westlake 密钥填入官方端点。
2026-10-19 使用已有环境变量读取网关 `/models`，认证成功，可用 DeepSeek 模型为
`deepseek-flash`；旧配置中的 `deepseek`、`deepseek_pro` 不在本次返回的模型列表中。

网关公开的 `/api/pricing` 为该模型声明的接口是 `POST /v1/chat/completions`。
`--provider westlake` 通过会话内临时兼容器接到 Codex Responses，
详见 [Westlake 协议与验证范围](WESTLAKE.md#协议兼容)。密钥不会填入 DeepSeek 官方端点。

## 离线验证范围

已使用本机 Codex CLI `0.163.0`，在无凭据的临时 profile 中执行
`initialize` 和 `model/list`，确认两种模型及 `low / high / max` 推理选项均能解析。
该检查没有创建对话或启动推理；API 认证、服务端工具调用和实际解题仍需后续运行验证。

## 结果边界

此前的 GPT 试跑使用不同模型，保留为独立历史记录；DeepSeek 必须准备新的实验目录。
30,000 token 是停止新调度的门槛，不是硬限额，也不是已经校准的 DeepSeek 证明预算。
只有在同一冻结计划内完成证明任务和完整 Lean 验收后，才讨论模块策略的效果。

接口与模型元数据依据 2026-10-19 查阅的官方资料：

- [DeepSeek Codex 接入](https://api-docs.deepseek.com/quick_start/agent_integrations/codex)
- [DeepSeek 模型与能力](https://api-docs.deepseek.com/quick_start/pricing)
- [DeepSeek 推理强度映射](https://api-docs.deepseek.com/guides/thinking_mode)
- [OpenAI Docs：Codex 配置参考](https://learn.chatgpt.com/docs/config-file/config-reference)

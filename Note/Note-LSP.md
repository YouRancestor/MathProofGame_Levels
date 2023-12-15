# Language Server Protocol 笔记

## 头部

与HTTP头部风格相同，以"\r\n\r\n"结尾。

头部可使用的字段：
| 字段名 | 类型 | 描述 |
|-|-|-|
|Content-Length | number | 请求内容的字节数 |
|Content-Type | string | 内容部分的 mime type。 默认值为 application/vscode-jsonrpc; charset=utf-8|

## 内容部分

使用[JSON-RPC](http://www.jsonrpc.org/)格式描述。

```json
Content-Length: ...\r\n
\r\n
{
	"jsonrpc": "2.0",
	"id": 1,
	"method": "textDocument/completion",
	"params": {
		...
	}
}
```
## 请求

### initialize
initialize 是第一个请求，服务器返回 InitializeResult 前不能发送其它请求或通知。
initialize 前，发送其它请求会返回错误；允许发送 exit 通知使服务器退出，其它通知则会被忽略。
响应 initialize 过程中，服务器可以向发送 window/showMessage, window/logMessage, telemetry/event 通知和 window/showMessageRequest 请求。
如果客户端在 initialize 请求的参数中设置了 token ，服务器可以向客户端发送$/progress。
initialize 请求只能发送一次。

## 通知
```json
{
	"method": "$/...",
	"params": {
		"id": ...
	}
}
```
```json
{
	"method": "$/progress", // 进度
	"params": {
		"token": ..., // integer|string
		"value": {
			...
		}
	}
}
```

## 流程

1. initialize 初始化
	- 请求参数
		- processId LSP-Server父进程ID
		- clientInfo 客户端描述
		- rootPath, rootUri 根目录
		- workspaceFolders 工作区目录
	- 响应参数

1. initialized 初始化完成

1. 回复服务器 id 为 register_ilean_watcher 的请求

1. textDocument/didOpen 打开文档，worker 启动

1. $/lean/rpc/connect 获取 sessionId

1. $/lean/rpc/call Lean.Widget.getInteractiveGoals 使用上一步获取的 sessionId 获取目标 Goals

1. $/lean/rpc/keepAlive session 心跳保活（30秒超时）

1. textDocument/didChange 修改文档

1. textDocument/publishDiagnostics 全局提示（All Messages）（通知：S->C）

1. textDocument/documentSymbol 符号解析

1. textDocument/hover 获取符号定义注释

1. textDocument/definition 获取符号定义文件位置

1. textDocument/semanticTokens 获取符号定义范围
    用tokenTypes和tokenModifiers解析，解析方法见
	https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens
## Goal解析
	参考 vscode-lean4 项目 goals.tsx 文件中的 goalToString 函数

- hyps : InteractiveHypothesisBundle := 假设

- type : CodeWithInfos := Goal类型

		/-- Invariants:
		- non-empty
		- no adjacent `text` elements (they should be collapsed)
		- no directly nested `append`s (but `append #[tag _ (append ..)]` is okay) -/

	- text : 无格式文本

	- append : 数组（容器），元素为text或tag，或append

	- tag : 格式化的符号（容器）
		
		- info : WithRpcRef Lean.Elab.InfoWithCtx := The `Elab.Info` node with the semantics of this part of the output.

- ctx : WithRpcRef Elab.ContextInfo := Metavariable context that the goal is well-typed in. 

- goalPrefix : String := Goal前缀 The symbol to display before the target type. Usually `⊢ ` but `conv` goals use `∣ `
  and it could be extended.

- mvarId : MVarId := Identifies the goal (ie with the unique name of the MVar that it is a goal for.)





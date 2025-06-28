# 安装脚本

- stages 定义安装的阶段，按顺序执行，如无定义，则默认执行unpack和lake_print_paths阶段。
 * unpack 内置阶段名，无需定义步骤，行为是解db包
 * lake_print_paths 内置阶段名，无需定义步骤，行为是对definition执行"lake print-paths"命令
- steps 定义各安装阶段的具体步骤
 * 每个阶段的步骤对应一个列表，按顺序执行
 * 每个步骤有固定的类型字段"type"

## steps 类型

- copy: 异步复制文件，参数为"src"和"dst"，"src"为相对路径，相对于db文件所在目录，"dst"为目标文件或目录的绝对路径，可以使用变量。"dst"添加到卸载时需要删除的文件列表中记录。

- cmd: 执行命令，参数为"cmd"和"cwd"，"cmd"为要执行的命令，"cwd"为执行命令的目录绝对路径，可以使用变量。"dst"（可选）为卸载时需要删除的文件列表。
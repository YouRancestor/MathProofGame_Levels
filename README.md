# 关卡与答案

用于设计教程、关卡，生成关卡文件。

## 目录结构

- Tutorial: 教程关，含答案，介绍各种 tactic 用法。

- Definition: tactic、公理、运算等的定义。

- Collection: 正式关卡，含答案。关卡中的命题作为收藏品，玩家完成证明后可以在后续的关卡中使用。

- Output: 生成的关卡文件（去掉证明过程，用 sorry 代替）。将该目录文件移动至 save_dir 模拟用户环境进行测试，通过后，在此目录对 package 进行 build 后打包。

- Note: 笔记和练习。

## 命令

### 初始化

```bat
REM TODO: copy, git config --local, git init, git add, git commit 初始化仓库
lake "print-paths" "Init" "Definition"
git commit -m "init"
REM TODO: 部署Tutorial关卡
lake "print-paths" "Init" "Tutorial.Notation"
```
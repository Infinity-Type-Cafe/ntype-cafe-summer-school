# Coq的安装方法

这次课程中会介绍Coq的使用方法．因为课程只对Coq做简单的介绍，听讲者可以不自行安装Coq，只观看讲师的演示．如果希望跟随讲师一起演示，则需要自行安装Coq．这里介绍一些Coq的安装方法．

## 使用在线版本jsCoq
这一方法最为简单，不需安装任何．只需前往[该页面](https://jscoq.github.io/scratchpad.html)便可使用．

缺点在于：执行速度可能较慢，且依赖网络环境．

## 使用Coq平台（macOS或Windows）
在macOS或Windows上最简单的安装方法是使用Coq平台安装器．安装器可以从[这里](https://github.com/coq/platform/releases/tag/2022.09.1)下载到．

## 通过opam安装（Linux、macOS及Windows Subsystem for Linux）
如果你已经使用OCaml，通过opam安装是最简单的．当然，即使你没有使用过OCaml，opam的安装也并不复杂．如果你在macOS或Linux环境，可以直接安装opam．

如果在Windows环境，则需要先安装Windows Subsystem for Linux（WSL）．如果你运行的Windows版本高于Windows 10更新21H1或Windows 11更新21H2，直接从Windows商店安装WSL即可，接着参照Linux下的安装方法继续安装．除了WSL本体以外，你还需要从商店里安装一个发行版．如果你使用Linux的经验较少，可以安装Ubuntu 22.04.2 LTS或OpenSUSE Tumbleweed发行版．

如果你使用的Windows版本较旧，安装步骤可以参考微软的[官方文档](https://learn.microsoft.com/zh-cn/windows/wsl/install)．

### macOS用户
如果你已经使用Homebrew或MacPorts包管理器，直接通过包管理器安装opam即可．Homebrew用户可以使用如下命令：
```console
$ brew install opam
```

而MacPorts用户则可使用：
```console
$ port install opam
```

若你没有也不打算使用包管理器，可以用官方的安装脚本安装二进制版本：
```console
$ bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
```

OCaml原生支持AArch64架构，并且安装脚本和opam都会自动检测架构，所以使用M1/M2设备的读者也不必担心．

### Linux用户和WSL用户
许多Linux发行版的库中都有opam．若你使用Arch、Debian、OpenSUSE、Fedora、CentOS或Red Hat发行版，直接通过你的包管理器安装`opam`包即可．
例如在Arch中只需在命令行中执行：
```console
# pacman -Syu opam
```

若你使用的是Ubuntu（版本大于18.04 Bionic Beaver），则需要先添加一个PPA：
```console
# add-apt-repository ppa:avsm/ppa
# apt update
# apt install opam
```

（命令行的`#`前缀指该命令需要管理员权限，通常在命令前添加`sudo`即可．）

其它Linux发行版则可使用官方安装脚本．

### 安装Coq
安装opam后，你需要先初始化opam:
```console
$ opam init
$ eval $(opam env)
```

接着便可以安装Coq：
```console
$ opam pin add coq 8.17.1
```

opam会自动处理PATH等问题，因此只需把一切交给opam就可以了．

## 配置Coq开发环境

### 使用Emacs和Proof General
如果你已经懂得Emacs编辑器基本的使用方法，那么Emacs的Proof General插件无疑是最适合Coq的开发环境．如果你使用Linux或WSL，Emacs可以直接通过你使用的发行版的包管理器安装，包的名称通常是`emacs`．

例如，在Arch Linux中是：
```console
# pacman -Syu emacs
```
在Ubuntu中是：
```console
# apt install emacs
```

如果你是Mac用户，你可以从Homebrew或MacPorts安装GNU版本的Emacs，也可以安装[Aquamacs](https://aquamacs.org/)．

首先，若你还没有如此做的话，请先配置Emacs使得其能够使用MELPA库．在你的`.emacs`或`.emacs.d/init.el`中添加如下的代码：
```elisp
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)
```
如果你身处中国大陆，可以考虑将上面的URL更换为MELPA的清华镜像：`http://mirrors.tuna.tsinghua.edu.cn/elpa/melpa/`．

接着，输入`M-x`（在Windows和Linux上`M`是Alt，在macOS上`M`是Option）启动命令模式，并输入`refresh-package-contents`回车．我们也常将此操作简写为`M-x refresh-packge-contents RET`．这将刷新Emacs的包数据库缓存．接着，输入`M-x install-package RET proof-general RET`，Emacs便会开始安装Proof General．

接下来，你还可以输入`M-x install-package RET company-coq RET`安装Company-Coq包．这不是必须的，但会让你的体验更好．Proof General的操作方式可以参考其[官方文档](https://proofgeneral.github.io/doc/master/userman/)．


### 使用CoqIDE
如果Emacs和Proof General的配置和使用对你来说太繁杂，那Coq也有一个自带的开发环境CoqIDE．如果你通过Coq平台安装了Coq，那么CoqIDE应当已经被安装了．如果你通过opam安装Coq，那么只需输入：
```console
$ opam install coqide
```
即可安装CoqIDE．

### 使用Visual Studio Code
不论你使用的是Windows、Linux还是macOS，都可以用Visual Studio Code作为Coq开发环境，为此你需要安装并配置VSCoq插件．通常来说，你至多只需要配置`"coqtop.binPath"`一个参数即可．

如果你使用WSL，则还需要安装WSL插件．具体操作方法可以参考微软的[官方教程](https://learn.microsoft.com/zh-cn/windows/wsl/tutorials/wsl-vscode).

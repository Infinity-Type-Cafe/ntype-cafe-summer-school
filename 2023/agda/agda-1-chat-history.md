```
| 2023/7/5
|
o- 19:51 JOJO 
| 等开始
|
o- 19:52 JOJO 
| 这个主题好好看
|
o- 19:52 JOJO 
| 是的
|
o- 19:52 摸 
| vsc
|
o- 19:52 JOJO 
| 哦哦
|
o- 20:00 oCaU 
| https://agda-zh.github.io/PLFA-zh/
|
o- 20:04 JOJO 
| 准备过程可以不做吗
|
o- 20:08 小大圣 
| 游标卡尺是吧(x
|
o- 20:17 灯夜 
| 提问:如何区分定义和命题?比如这个是加法的定义还是说某个名字叫 + 的命题的证明?
|
o- 20:19 启源 
| 这里是加法的定义,一个 operator,从nat nat 到 nat。命题是类型,这里显然不是在定义类型
|
o- 20:20 灯夜 
| Nat -> Nat -> Nat也是一个类型,命题即类型
|
o- 20:21 启源 
| 类型具有类型 Type,比如 0 + 1 = 1 + 0 这个具有类型 Type (或者 Prop 在 Coq 里),这里的 = 具有类型 nat -> nat -> Type
|
o- 20:23 启源 
| (nat -> nat -> nat) : Type 但是 + : nat -> nat -> nat
|
o- 20:28 灯夜 
| 也就是
| Prop:Set
| add:Type : Set
| 层级不一样,明白了
|
o- 20:47 灯夜 
| 嗯,解释前面的
|
o- 20:50 QDelta 
| sym
|
o- 20:50 Wtz_LASR 
| sym
|
o- 20:51 Wtz_LASR 
| 可能库做了处理吧
|
o- 20:51 Wtz_LASR 
| 奥
|
o- 20:53 Wtz_LASR 
| suc (+-swap m n)
|
o- 20:55 Fain 
| agda在定义了data以后会生成相应的ind或者rec方法吗
|
o- 20:56 Fain 
| ok,谢谢,明白力
|
o- 21:00 灯夜 
| 不会配置standary-
| lib
|
o- 21:01 灯夜 
| wsl ubuntu
|
o- 21:01 Wtz_LASR 
| 就用原版PLFA前言的方法配置就行
|
o- 21:02 Rroscha 
| https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md
|
o- 21:02 灯夜 
| 这个配好了
|
o- 21:03 灯夜 
| 但ladga.md里面的导入没生效
|
o- 21:03 LXL 
| (有没生效的报错截图么)
|
o- 21:03 灯夜 
| 我直接clone的仓库
|
o- 21:04 CAIMEO 
| vsc 的 agda-mode 报错 Server initialization failed 咋办 (
|
```

o- 21:04 史豪

<img src="./images/agda-1-史豪 21:04.png" width="70%">

```
|
o- 21:04 史豪 
| dengye de pic
|
o- 21:05 QDelta 
| 要先open Data.Nat才能直接用N吧
|
```

o- 21:05 灯夜

<img src="images/agda-1-灯夜 21:05.png" width="70%">

```
|
o- 21:05 猫姐姐 
| Agda内部是怎么判别定义性相等的?它应该要进行展开,但需要展开到何种程度?比如判断refl: 2^100=2^100,需要展开2^100次吗?
|
o- 21:06 猫姐姐 
| 另外似乎有一个叫WHNF范式的东西,这个需要看哪些资料?
|
o- 21:06 LXL 
| clone下来的plfa的完整地址像是plfa/src/plfa/part1 然后balabala来着?
|
o- 21:06 灯夜 
| 嗯
|
o- 21:08 pe200012 
| 符号计算?
|
```

o- 21:08 灯夜 

<img src="images/agda-1-灯夜 21:08.png" width="70%">

```
|
o- 21:08 灯夜 
| 路径是对的
|
o- 21:08 pe200012 
| WHNF: weak head normal form
|
o- 21:09 LXL 
| (我那个是回复史豪的)
|
o- 21:11 猫姐姐 
| Lean 4里面我知道有
|
o- 21:11 pe200012 
| 就是一个 thunk 只解出一个头部
|
o- 21:11 灯夜 
| 报错截图就是
|
o- 21:11 灯夜
```

<img src="images/agda-1-灯夜 21:11.png" width="70%">

```
|
o- 21:11 yinfeng 
| N 找不到的那个把 import Data.Nat using 改成 open import Data.Nat using 就可以了
|
o- 21:13 灯夜 
| 加open就可以了
|
o- 21:13 灯夜 
| 解决了,加个open就没问题了
|
o- 21:13 数学主义 
| 我用 1.7.2 没有报错
|
o- 21:13 Usamoi 
| lastest版本的Agda对应的std是1.7.2(
|
o- 21:14 pe200012 
| 最新大概率是 2.7.2.2 ()
| 
o- 21:16 pe200012 
| 我指的 Agda 的版本()
|
o- 21:17 pe200012 
| 没事了()我看错了
# 裸态明显改变，但允许的源引力观测保持：精确的代数验收

原 [constraint_states/RELATIONAL.md](../../constraint_states/RELATIONAL.md) §5 已证明零模去相干的 A_P 观测商及给定 FLRW 影响泛函保持。本页复用这一原则；新增的是薄层秩二态的21级平滑完整记录、严格裸态扰动和有限资源，以及本实际非静态历史的具体应用，不将观测商原理再次计为新发现。

## 1. 要保留的物理内容应明确到观测代数

旧固定完整裸态的排除仍正确。SMOOTH_PREPARATION的输出Dtr>0.8。
本页另证明：在当前自由、minimal、massless源模型中，该非选择输出仍与原态
在全部允许的source derivative/stress观测上相同。
这不是说两态绝对物理相同，也不把源相同扩大到装置总应力相同。

在同一incoming表示
\[
 {\cal H}_S=L^2(\mathbb R^2_P)\otimes{\cal F}_{high},\qquad
 {\cal A}_P=L^\infty(\mathbb R^2_P)\bar\otimes B({\cal F}_{high})
           =\{P_1,P_2\}'.
\tag{O1}
\]
正常态在此代数的限制用可积正迹类operator-fieldσ(P)表示：
\[
 \omega(O)=\int d^2P\,{\rm Tr}_F[\sigma(P)O(P)].
\]
这是von Neumann子代数上的正常泛函，不是声称存在完整Hilbert空间上的
“连续动量对角密度矩阵”。不要把分布核δ(P−P′)错误称作迹类算符。

## 2. 完整读出的精确保留引理

设逐P有[σ(P),Hhigh]=0，且M_j(P)=m_j(α[P²/(2A³)+Hhigh+Ec−Ebar])，
Σ_j|m_j|²=1。则
\[
 \sum_j M_j(P)\sigma(P)M_j(P)^\dagger
 =\sigma(P)\sum_j|M_j(P)|^2=\sigma(P).               \tag{O2}
\]
所以对每个有界O∈A_P，Trρ′O=TrρO。

旧薄层态满足条件：
\[
 \sigma(P)=(1-p)|\psi_0(P)|^2|0\rangle\langle0|
          +p|\psi_2(P)|^2|A_\pm\rangle\langle A_\pm|,
\]
两高模向量各是Hin,high本征向量。P4构造因而给同一A_P限制。
这是一项关于给定输入态的restriction保持；并非channel在A_P上是恒等映射。
若输入在同一个P fiber内含不同Hhigh能量的相干，读出一般会改变其限制。

## 3. 当前实际完整应力历史属于该代数

质量为零、minimal耦合的常数场是每个背景的解。
在本实际齐次历史上，TENSOR_NOISE明确给
∂Φ_i=P_i z+high modes，不含Q。
因此这些导数字段的有界Weyl代数属于A_P；
所有已定义的平滑Wick应力矩也由其共同域极限得到。
O2及同一正常光滑态的有限矩条件给
\[
 \langle T(F_1)\cdots T(F_m)\rangle_{\rho'}
 =\langle T(F_1)\cdots T(F_m)\rangle_\rho
\tag{O3}
\]
对已证明存在的每个有限乘积成立，特别包括完整mean、绝对tensor N、
source charge及六个global momentum混合块。

在共同端点和已实现的相对传播子V[g_-,g_+]存在且属于A_P的历史类上，
\[
 {\cal F}_{\rho'}[g_+,g_-]
 ={\cal F}_{\rho}[g_+,g_-].                         \tag{O4}
\]
原物理φ,π frame的shift对称性使已实现传播子强对易P。
ACTION_BOUNDARY先作同一个有限截止端点运输，再在合法定义域取极限。
O4不自行证明任意非齐次几何历史的无限模implementer、相位或renormalized CTP存在；
这些存在责任不能由[H,P]=0的形式式跳过。

准备中的α、C、bins和e_N固定在incoming frame。
不随比较几何重新选择；否则不是同一准备的响应。

## 4. 具体有限维正负控制

新exact checker取P有3个标签、high有2个能级，E_P=diag(1,2,3)，
Hhigh=diag(0,1)，C=E_P+Hhigh−5/2。
u0=(|P2〉+|P3〉)|N0〉/√2，
u2=(|P1〉+|P2〉)|N1〉/√2，
ρ=(|u0〉〈u0|+|u2〉〈u2|)/2。
两支C律相同为±1/2。按C符号记录后，
Dtr=1/2但A_P的全部12个矩阵基元期望完全相同。
同一channel对I_P⊗σx的dual作用非恒等；
同一P处跨high能量相干的反例亦改变。
这个有限模型检查代数逻辑，不能代替O1–O4的全场证明。

## 5. 对下一任务的实际改变

因此“完整裸态必须相同”比“当前源的全部引力耦合观测相同”更强。
我们现在有一个正常联合源—记忆态，保持当前源的全部允许非选择应力统计，
同时产生可计算的荷记录，代价是裸态的Q/φ可区分内容改变。

还不能签收的内容：
记录条件j一般改变条件源应力；装置、控制器与相互作用贡献没有消失；
记忆Zmem尚不是geometry charge；mass或非minimal φ²耦合破坏本页的适用条件；
有限局域实现还有SMOOTH_PREPARATION的因果门槛。

下一步应直接审查真实总作用量和总source下的constraint列，
无需继续尝试已经排除的“完整裸态完全保持且记录C”。

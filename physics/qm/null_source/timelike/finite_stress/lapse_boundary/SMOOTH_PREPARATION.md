# 允许改变态的正常21级记录：精度、扰动、资源及局域性

本页继承旧薄层态与C=α(Hin−Ebar)，α=2/(3V0A)，其谱律
dμ(c)=B^−1 w(c/B)²dc，B=ασ>0，支持[−B,B]。
w(x)=Z^−1/2 exp[−1/(1−x²)]，|x|<1，外为0。
全部记录在同一incoming Hilbert/frame定义一次，再沿合法共同场演化运输。
这里不是把记忆读数Zmem认作几何荷。

## 1. 固定支撑的排除如何定量延续

P为旧秩二源态支撑，旧精确压缩恒等式P f(C)P=μ(f)P保留。
对于任意正常联合态R，source边缘ρ′，ε=Dtr(ρ′,ρold)，
δ=1−Tr R(P⊗1)≤ε。
取载体侧自伴读数Zmem及success投影E=1{|C−Zmem|≤r}；
两个谱测度作用于独立因子。若q=Qμ(2r)=sup_z μ([z−r,z+r])，则PEP≤qP。
设s=Tr RE>q，有精确的两投影角度界
\[
 \boxed{\epsilon\ge\delta\ge
 [\sqrt{s(1-q)}-\sqrt{q(1-s)}]^2.}                 \tag{P1}
\]
证明：纯化R，令u=Pψ/||Pψ||及t=〈u,Eu〉≤q。
投影到E及1−E后用Cauchy–Schwarz，
√(1−δ)≤√(ts)+√((1−t)(1−s))
≤√(qs)+√((1−q)(1−s))，平方整理即P1。
这不依赖有限方差、乘积态或先前未发生相互作用。

Z≥exp(−8/3)，sup w²≤exp(2/3)<2；
故r=B/20时q<1/5。
s≥19/20要求
\[
 \epsilon>{77-4\sqrt{19}\over100}>0.59;
 \qquad s=1\ \Longrightarrow\ \epsilon>4/5.       \tag{P2}
\]
旧固定裸态ε=0的排除是此界的端点，不再重复尝试。

## 2. 一个实际正常、所有结果均保留的构造

n=21，中心z_j=−B+(2j−1)B/n，j=1…n；
内部边界b_j=−B+2Bj/n，过渡半宽τ=B/420。
S(y)=∫_{−1}^y w(t)²dt，在区间外平滑延为0、1。
θ_j(c)=πS((c−b_j)/τ)/2。
按能量从低到高依次施加相邻实平面旋转，
\[
 U(c)=R_{n-1,n}(\theta_{n-1}(c))\cdots R_{1,2}(\theta_1(c)),
 \quad m(c)=U(c)|1\rangle .                         \tag{P3}
\]
约定R将低编号基矢转为cosθ|j〉+sinθ|j+1〉。
由于过渡区互不相交，每个c最多有两个相邻非零m_j；
各m_j实、C∞，Σm_j²=1。
由谱演算U(C)为明确正常联合酉，和C强对易。

原两支在P动量表示中的联合波函数为
\[
 \Psi_N(P)=\psi_N(P)\otimes m(C(P,N)),\qquad
 R=(1-p)|\Psi_0,0\rangle\langle\Psi_0,0|
       +p|\Psi_2,A_\pm\rangle\langle\Psi_2,A_\pm|.    \tag{P4}
\]
源输出ρ′=Σ_j m_j(C)ρold m_j(C)。
记忆的非对角项保留在P4，不用不存在的“连续能量对角迹类态”替代。
所有结果j属于同一非选择输出；无失败项被删去，无后选择。

Zmem=Σ_j z_j|j〉〈j|给
\[
 \Pr(|C-Z_{\rm mem}|\le B/n+\tau=B/20)=1.           \tag{P5}
\]
因为连续非退化μ不能集中于有限个z_j，残差方差严格正。
对称构造使两者均值零；μ2=∫x²w²>1/128，故
\[
 0<\operatorname{Var}(C-Z_{\rm mem})<B^2/400
 <{8\over25}\operatorname{Var}C.                   \tag{P6}
\]
μ2下界可由x∈[1/4,1/2]及其负区间、Z≤2e^−2直接得到
μ2≥e^−2/3/64>1/128；上界μ2<1/3由偶且径向严格递减权重与均匀分布比较得到。
P2要求此明确构造Dtr>0.8；它不可能被称为保留完整裸态。

## 3. 全部中间量可计算，数值诊断和严格界分开

令
\[
 G_{ij}=\int m_i(c)m_j(c)d\mu(c),\quad
 b_i=\int m_i(c)d\mu(c).
\]
记忆密度是G，概率Gjj。联合谱特征函数是
Σ_j∫m_j² exp[i(sc+tz_j)]dμ(c)。
旧支向量减去输出正算符的唯一正本征值λ满足
\[
 \lambda=1-b^T(\lambda I+G)^{-1}b,\qquad D_{\rm tr}=\lambda.
\tag{P7}
\]
两个正交壳层有相同G、b，因此混合权重不改变此trace distance。
支撑泄漏为δ=1−Σb_i²，且λ≥δ。
P7由rank-one resolvent恒等式给出；零本征空间用λ>0的逆处理。

G,b、μ2、残差及λ可用分段Gauss积分作可复现数值诊断。
本cohort同时改变阶数观察收敛；没有独立积分余项证明时，
这些小数不标成向外包围。严格P1–P6与下面有限资源界不依赖此诊断。

## 4. 平滑保留有限正则资源，尖锐分箱则失败

各ψ_N原为紧支C∞环包，c(P,N)光滑，故P4在动量域仍为C∞紧支。
每个有限零模Q、P多项式矩存在；高模Hadamard结构不变。
梯度正交恒等式Σm_j m_j′=0且|S′|<2给
\[
 \sum_j(m_j')^2<\pi^2/\tau^2.
\]
直接对P4求P导数，
\[
 \Delta\left\langle\sum_iQ_i^2\right\rangle
 ={2\alpha^2 E_z\over A^3}\int\sum_j(m_j')^2d\mu
 <{2\pi^2\alpha^2E_z\over A^3\tau^2}.              \tag{P8}
\]
其中积分中e_N+c/α的c奇项因对称性消去。
对D=Σ_i(Q_iP_i+P_iQ_i)/2，
\[
 \Delta\operatorname{Var}D
 =4\alpha^2\int[(1-p)(e_0+c/\alpha)^2
             +p(e_2+c/\alpha)^2]\sum_j(m_j')^2d\mu . \tag{P9}
\]
这是严格正、有限的代价，不是已计算的完整装置能量。
原Robertson关系仍给
Var(C−Zmem) Var D≥α²Ez²，故此精度至少需要Var D>400Ez²/σ²。

若把m_j改为尖锐区间指示函数，则ψ_N在非零边界有跳跃，Q²积分发散。
尖锐分箱可以作为抽象正常CP映射，不能当作本有限正则资源制备。
21个记录可编码在5个qubit的子空间中；这不是包括控制器的5qubit真实装置。

## 5. 同一源—读数实际混合块

记k=Cov(C,Zmem)=Σ_j∫c z_j m_j²dμ。
由条件壳层律、grade与对称性，
\[
 \operatorname{Cov}(Z_{\rm mem},\bar T_X[f])=(k/\alpha)L_f,
 \qquad \operatorname{Cov}(Z_{\rm mem},N)=0.
\tag{P10}
\]
它是真实P4中产生的相关，不是任意填写协方差矩阵。
但Zmem仍是记忆读数，没有得到Einstein lapse变分的几何荷身份。
条件于某个j后，源profile及其mean stress一般改变；
不能说每个读数条件分支都沿原同一U继续满足原平均Einstein方程。

## 6. 精确全局仪器的局域性门槛

本U(C)作为全局谱酉合法，但不是已经由有界时空区域中的耦合推出。
若候选紧耦合区K的因果补含一个静态incoming空间开集O，
局域测量框架要求诱导system effect与O的局域代数对易
（Fewster–Verch，https://arxiv.org/abs/1810.06512，Theorem 3.3）。

取中间记录effect f11(C)=m11(C)²。它在c=0附近为1，远离中心窄带为0。
在O中选局域动量测试π(F)，使其某个k≥2谐波系数非零。
在零模动量环包的开邻域及vacuum→1_k矩阵元上，
[f11(C),π(F)]比例于
f11(c0(P)+αεk)−f11(c0(P))。
由于εk/σ≥100，前者为0而后者非零。用正常光滑P波包即可见非零，
不用动量δ本征态。有限粒子Schwartz共同核上的不对易，
亦意味着某个相应有界局域Weyl算符不对易。

所以这个对所有输入态定义的精确全局effect不能由上述有非空因果补的紧局域耦合实现。
这不排除态依赖近似、空间延展控制器、或因果补为空的长准备过去；
它要求这些方案单独构造并计入应力。P4的正常性与局域装置可实现性是两项不同验收。

## 7. 有限读数的严格资源下界，及21级的最小性

这里n指真正memory-only自伴指针Zmem的互异离散谱值数，
各投影可以简并；不是任意continuous POVM的outcome数。
允许任意正常源—记忆相关，只固定源C的当前谱律μ。
令M=||dμ/dc||∞<2/B。
对任意λ、r≥0，将joint分量μ_j(A)=TrR[1_A(C)⊗Π_j]相加，得到
\[
 \Pr(|C-Z_{\rm mem}-\lambda|\le r)
 \le\mu\!\left(\bigcup_{j=1}^n[z_j+\lambda-r,z_j+\lambda+r]\right)
 \le\min(1,2nMr).
\tag{P11}
\]
这不使用固定完整裸边缘或独立性。以λ取残差均值并积分尾概率，
\[
 \operatorname{Var}(C-Z_{\rm mem})
 \ge\int_0^{1/(2nM)}2r(1-2nMr)dr
 ={1\over12n^2M^2}>{B^2\over48n^2}.
\tag{P12}
\]
因此本21级构造有明确双边资源预算
B²/21168<Var(C−Zmem)<B²/400。
下界依赖n，没有声称所有任意大记忆仍有同一正下界。

进一步限定本页连续spectral-record类m_j(c)，Σ|m_j|²=1，
且sure误差≤r=B/20。μ密度在(−B,B)严格正；
success a.e.与连续性迫使m_j在|c−z_j|≥r的内部边界上也为零。
所以open intervals(z_j−r,z_j+r)必须覆盖整个(−B,B)。
n<20总长度不足；n=20总长度恰2B，不能外溢或正长度重叠，
只能相接铺满，但每个接点均不在任何open interval内，矛盾。
故n≥21；P3的21级正过渡宽构造达到这个数。

这是明确平滑有限谱记录类的最小level数，
不是所有量子仪器、带失败概率的程序、连续POVM或量子引力装置的普遍最小维数。
P11/P12若用到条件后选择态，必须换用其实际条件谱律，不能偷留原μ。

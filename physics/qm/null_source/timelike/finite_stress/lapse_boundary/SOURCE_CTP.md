# 实际源的 CTP 二阶块、初始荷关联和六个动量荷

此页接合 ACTION_BOUNDARY 与 TENSOR_NOISE，所有导数均在同一实际U、同一incoming态和同一AE处方上。
得到的是源侧的块，不能把它命名为尚未构造的几何边界密度C_Y或K。

## 1. 真实 lapse—scale 顶点

取ν=δN、w=δlog a，N=1，紧支测试避开端点；若触边则保留ACTION_BOUNDARY的密度与gluing导数。
由 δS=1/2∫√−g T^ab δg_ab，真正顶点为
\[
 J[\nu,w]=\int V_0a^4[-(\nu+w)\bar\rho+3w\bar p]d\eta.
\tag{C1}
\]
这里固定conformal lapse改变a也改变proper lapse，不能漏掉−wρ。
令 jρ=−V0a⁴(ν+w)，jp=3V0a⁴w，
TENSOR_NOISE的绝对矩阵直接给 N_J=N(j,j)。
有限截止上CTP展开为
\[
 \log{\cal F}
 =i\langle J_\Delta\rangle+i\,j_\Delta Rj_c
   -\tfrac12N(j_\Delta,j_\Delta)
   +\hbox{local metric/state contacts}+O(\delta g^3),
\tag{C2}
\]
R_XY=iθ〈[T_X,T_Y]〉，采用δH=−jT约定。实部接触项按同AE处方取极限；
N已经是合法的全场分布，但不能由此删除或任意指定local contacts。

## 2. 二阶差与旧精确影响泛函相合

实际pair系数为
\[
 B_{J,k}=\int V_0a^4[-(\nu+w)B_{\rho k}+3wB_{pk}]d\eta
 =-\int[\nu(r_k^2+\omega_k^2v_k^2)/2+w'v_kr_k]d\eta.
\tag{C3}
\]
第二式由(vr)′=r²−ω²v²及w的紧支性，直接从原canonical作用量得到。
若相对酉V采用V†aV=αa+βa†，其一阶β1=2i B_J*。
旧BOUNDARY_STATE §7a的精确齐次影响因子展开于是给
\[
 \Delta\log{\cal F}^{(2)}
 =-pd|\beta_1|^2=-16p|B_{J,2}|^2
 =-\tfrac12\Delta N(J,J),\qquad d=4.
\tag{C4}
\]
它在实际非静态背景上成立。两态的mean、平均commutator以及由相同W2决定的局部接触和mean-response相同；
新增差只在此noise项。没有把旧精确影响泛函本身再次计作新发现。

对anchored时间微分同胚ν=f′、w=hf，f紧支，
C1配对后积分分部恰为 V0a⁴f[ρ′+3h(ρ+p)]，故J的中心化部分与B_J均零。
这是实际Ward负控，须同时变化lapse和scale；只令ν=f′而不带w=hf不是非静态纯gauge。
静态极限Bρ=0，单独lapse不产生此差；w顶点给B_J=−ω∫w e^−2iωη。

## 3. 绝对噪声与交换子的量子相容性

k=2令S±=16+(24±16)p、M=16+8p。未对称二阶型为
\[
 W_{\rm pair}(f,g)
 =S_\pm\operatorname{Re}(B_fB_g^*)+iM\operatorname{Im}(B_fB_g^*)
 ={S_\pm+M\over2}B_fB_g^*
  +{S_\pm-M\over2}B_f^*B_g .
\tag{C5}
\]
两个系数均非负：plus为16+24p和16p，minus为16+8p和0。
所以不只是N为实正型，N+〈comm〉/2还是正的复Gram型，满足Robertson矩阵条件。
两测试的pair行列式差为(S²−M²)[Im(B_fB_g*)]²≥0。
minus仅这个pair子块饱和；profile、number、其余高模仍有自己的正项。
高真空每个k有S=M=4k²，合法平滑极限保正。没有指定互相独立的经典ρ、p噪声。

## 4. 初始源荷—未来全张量混合块

α=2/(3V0A)，C=ασX，L=A³/(V0a⁶)。由X与N条件律的独立、pair数目分级及高真空，
\[
 \operatorname{Var}C=\alpha^2\sigma^2\mu_2,\qquad
 \operatorname{Cov}_{sym}(C,\bar\rho(\eta))
 =\operatorname{Cov}_{sym}(C,\bar p(\eta))
 =\alpha\sigma^2\mu_2 L(\eta).
\tag{C6}
\]
平均交换子为零，不宣称[C,T]这个算符为零。
各向同性直接给局域版本
\[
 \operatorname{Cov}_{sym}(C,T_{ab}(x))
 =\alpha\sigma^2\mu_2L(\eta)(n_an_b+s_{ab}),\qquad s_{ab}=g_{ab}+n_an_b.
\tag{C7}
\]
flux关联为零，两个NOON符号相同。
对C1，
\[
 \operatorname{Cov}(C,J)
 =-\alpha A^3\sigma^2\mu_2\,\delta I,\qquad
 \delta I=\int a^{-2}(\nu-2w)d\eta.
\tag{C8}
\]
这与旧W(A³σΔI)因子的混合二阶导数一致。它是真实源初始荷/未来源应力块，
不是另一个几何张量因子的初始相关量。

## 5. 六个完整空间 Killing 动量荷

对单位S³的任意Killing场ξ，真实charge为
\[
 J_\xi=\sum_i\int d\Omega\,\pi_i\,\xi^a\partial_a\phi_i
       =\sum_i\int d\Omega\,(q_i'-hq_i)\xi^a\partial_aq_i.
\tag{C9}
\]
div ξ=0且S³无边界使h项=−h/2∫ξ·∇q²=0，故raw/bulk frame给相同charge。
有限完整谐波截止上[Q_K,Jξ]=0；端点shear不能创建此动量荷。

不是仅仅ρ旋转不变：薄层每个支向量本身都是SO(4) singlet。
零模为空间常量，高模为真空，每个k=2 pair向量由Σ_m a_im†²产生。
完整四维实谐波表示D(R)正交，故此和不变。
因此所有六个生成元都满足
\[
 J_\xi|\psi_0,0\rangle=J_\xi|\psi_2,A_\pm\rangle=0,
 \quad \operatorname{Var}J_\xi=0,
 \quad \operatorname{Cov}(J_\xi,T(F))=0.
\tag{C10}
\]
严格的域论理由是向量由强连续群完全固定，故属于每个生成元的域且生成元作用为零。
齐次共同演化保持SO(4)；由C构造的平滑记录也强对易旋转，所以其完整联合态仍满足C10。

负控：具有同一W2的Gaussian thermal参考态却有
Var Jξ=2n(n+1)Tr Lξ²；单平面旋转Tr L²=2，给4n(n+1)>0。
TENSOR_NOISE的有限κ4恰将它抵消。把实际态Gaussian化会连这些全局动量约束也算错。

C10只关闭六个integrated Killing荷的源侧行及其混合块。
局部T_ni、其余vector harmonics、真实装置的动量源和几何动量约束仍需处理。

## 6. 本页闭环后的真正缺口

实际绝对source N、它与comm的量子相容性、初始source C混合列以及六个global momentum列已经明确。
它们必须作为同一态的组合输入。还没有构造的是能实现
C_geom−C_pre=C_source的正常几何—物质—装置态及其总作用量、全部局域约束与正窗因果解。
端点的坐标混合不能补齐这一缺口。更高非Gaussian累积量不能由二阶N自动恢复。

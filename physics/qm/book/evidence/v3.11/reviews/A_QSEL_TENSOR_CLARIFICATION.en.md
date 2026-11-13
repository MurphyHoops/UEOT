This extension concerns the registered elementary registers and the circuits they generate; it does not identify the systemwise direct-sum construction with a strong monoidal functor. Complete each nontrivial elementary register as above, while the empty register, or tensor unit, remains $\mathbb C$. Joint carriers use the **actual algebraic tensor product** of the completed algebras, for example $(M_d(\mathbb C)\oplus\mathbb C)\otimes(M_e(\mathbb C)\oplus\mathbb C)$. Its fully visible central block is $M_d(\mathbb C)\otimes M_e(\mathbb C)$; the direct sum of all other central blocks forms the hidden part and must not be silently replaced by one copy of $\mathbb C$. In general, write the input and output as $\widetilde{\mathcal A}=\mathcal A_{\rm vis}\oplus\mathcal A_{\rm hid}$ and $\widetilde{\mathcal B}=\mathcal B_{\rm vis}\oplus\mathcal B_{\rm hid}$. Discarding is the sum of the ordinary matrix traces over their central blocks. With no input or output register, the corresponding visible algebra is $\mathbb C$ and its hidden part is zero.

Any original complete CP instrument $\{\Phi_y\}$ with multiple input and output registers can act as originally specified on the visible joint block, with the extension

$$
\widetilde\Phi_y(\rho\oplus\xi)
=\iota_{\mathcal B}\Phi_y(\rho)+\Xi_y(\xi),
\qquad
\Xi_y(\xi)=w_y\operatorname{Tr}(\xi)\tau_{\mathcal B},
\quad w_y\ge0,\quad\sum_yw_y=1,
$$

where $\iota_{\mathcal B}$ embeds the visible block and $\tau_{\mathcal B}$ is any fixed normalized state of the actual output algebra; for a tensor-unit output choose $\tau_{\mathcal B}=1$. Every branch is CP, and their sum preserves the full input trace. Identity operations may instead use the identity extension on the hidden part, and discarding uses the full total trace. Extensions are chosen only for the registered generating operations; sequential, parallel and conditional circuits are then built by actual CP composition and actual algebraic tensor products. From visible preparations, $\xi=0$, so every such circuit retains its original visible branches and probabilities. The result establishes operational equivalence of reachable circuits. It does not assert that every original operational equation also holds on the added unreachable sectors, or that $\widehat{\mathcal A\otimes\mathcal B}=\widehat{\mathcal A}\otimes\widehat{\mathcal B}$. The completed theory may additionally allow preparations of hidden states, but they are outside the reachable preparation library fixed by this proposition.

# Growing finite carriers and a controlled blue-pulse omission

## Recovery and scope

The effective main was reread as `aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d`.
PRs 457 and 458 are merged. Their v31.11 / Kernel 1.11 source and receipts are
inherited at their original identities. No v31.12 branch, PR, or unpublished
workspace could be recovered. The present files reconstruct the narrow
interrupted scientific increment and obtain **new actual execution receipts**.
Statements about an earlier unpublished run are not treated as recovered evidence.
Core and `physics/interfaces/` are read-only; GI is excluded. Exactly three native
AI researchers A/B/C review the increment. Their review is internal AI review.

## One source, parameter and output

Keep the v31.11 system, number operator and finite untouched reference:
\(S=\mathbb C^2\otimes\ell^2(\mathbb N_0)\),
\(G=a^\dagger a+P_e\), \(\Pi_M=1_{G\le M}\), rank \(2M+1\).
Inputs may be entangled with R and satisfy \(\operatorname{Tr}G\rho_S\le\bar n\).
The chosen complex structure, Born rule, Fock representation and instrument
calculus are independent standard physical inputs P/S, not consequences of Core.

The common parameter is \(\theta=(q,\phi,\alpha,\beta)\), with
\(q\in[12/25,13/25]\) and \(s=1-q/2\). Pulse areas are dimensionless; a
laboratory coupling \(g(t)\) gives area \(\int g(t)dt\) when the Hamiltonian is
\(\hbar g(t)H\). Freeze separated pulses in this exact order:

\[
U_0=e^{-i\phi P_e},\quad U_1=e^{-i\alpha(\sigma_+a+\sigma_-a^\dagger)},\quad
B_\beta=e^{-i\beta(\sigma_+a^\dagger+\sigma_-a)},\quad V_1=B_\beta U_1,
\quad V_0=U_0.
\]

This is an exact mathematical model of effective controls. For an ion realization,
sideband resolution, rotating-wave and Lamb-Dicke approximations need their own
calibrated errors on the actually used energy domain. In particular a high
analytic cutoff does not establish Lamb-Dicke validity. No apparatus is claimed
to implement these assumptions with the numerical error margin below.

Use the same three-level degenerate logical flag as before, with prepared column
\((\sqrt{s(1-q)},\sqrt{sq},\sqrt{1-s})\). The controlled gates and complete
readout derive \(K_0=\sqrt{s(1-q)}V_0\),
\(K_1=\sqrt{sq}V_1\), \(K_f=\sqrt{1-s}I\).
Perform at most two steps, stop on f, retain `f,0f,1f,00,01,10,11`, and accept the
last four only. The raw source has backward effect \(H=s^2I\); this is computed
from the original instrument, not supplied as a certificate field. Its complete
conditional target is CPTP. The general postselection theorem remains separate.

Deployment uses the previous legal visible-history policy: first weight 1/2;
second weight 312/625 after 0 and 313/625 after 1. Its two label-1 marginals are
both 1/2 and its full path law is independent of unknown theta. The action coin
is the visible label. No hidden Kraus index, future outcome, unknown parameter or
additional parameter-sensitive in-run test is available. Nodes within each
observation fiber use the same weight; distinguishable histories may differ.
In the full implementation the same actual V gates
are used; in the reduced implementation the blue pulse is omitted and the same
actual U gates remain.

## Growth and physical preparation

The blue Hamiltonian has independent blocks \((|g,n\rangle,|e,n+1\rangle)\)
with coefficient \(\sqrt{n+1}\), and the singleton \(|e,0\rangle\).
Its graph-domain direct sum is self-adjoint. Hence
\(B_\beta\Pi_M=\Pi_{M+2}B_\beta\Pi_M\).
Red/phase/failure gates preserve the cutoff. At depth j use carrier \(H_{N+2j}\);
restrict the actual branch maps between these carriers. Every stopping block is
embedded into the common final Fock carrier. Source-derived branch completeness,
bounded classical tree composition, and trace-distance contraction yield the
same initial tail bound as Chapter 67. No fixed-cutoff preservation is asserted.
The fixed finite numerical example starts at N=1 and ends at N+4=5. It is not a
numerical proof for N=4095 or all trace-class inputs.

The physical preparation filter has pass block \(P\rho P\), where
\(P=\Pi_N\otimes I_R\), and failure block
\(\tau_S\otimes\operatorname{Tr}_S[(I-P)\rho(I-P)]\), with
\(\tau_S=|g,0\rangle\langle g,0|\). It records `prep_fail`; pass blocks retain
all seven original labels, including the zero failure blocks of a conditional
target. The conditional reference marginal on failure is not replaced by the
unconditional one. The ideal comparison is always-pass and keeps the same R.

For this **low spectral** filter, passing does not increase conditional mean G.
This corrects one overbroad sentence in both versions of section 67.5; it does
not relabel the old execution. General outcome conditioning can increase energy.
Reuse P-MICRO-02's sharp preparation bound
\(f(e)=(\sqrt{4e-3e^2}+e)/2\), where \(e=\bar n/(N+1)<1\).

## Frozen error and resource contract

Freeze \(\bar n=1,N=4095,|\beta|\le1/100\) and required full-CQ precision
\(1/20\) before computing the certificate. The blue bound is a separate
physical assumption: logical flag counts do not identify beta.
Complete-CQ distance includes record, failure, stop label, system and reference.

The previous path-law proof gives robust error 1/50 with shared actual gates.
For the reduced implementation, telescope against the **no-blue reference
paths**, whose conditional states retain the mean-energy bound. Since
\(H_b^2=G+I-2P_e\le G+I\), a single local omission costs at most
\(|\beta|\sqrt{\bar n+1}\). Weight by all visible prefixes; the mean number
of selected blue calls under the deployed policy is one. Thus the extra
two-step bound is \(|\beta|\sqrt{\bar n+1}\), not two times that value and
not the source's \(2q\) conditional count. The full sufficient bound is
\(1/50+f(1/4096)+\sqrt2/100\). An independent rational interval checker must
verify it before acceptance. Numerical tolerances control calculations only;
unknown gate, filter and detector errors are not assigned zero for nature.

For a complete source attempt, acceptance including preparation is \(s_Ns^2\).
Read-flag-first source blue calls have mean \(s_Nsq(1+s)\); compiled full blue
calls have mean \(s_N\). A coherently controlled implementation may schedule
the pulse in every attempted slot, with corresponding means \(s_N(1+s)\)
and \(2s_N\). These are different hardware cost contracts, despite identical
observable instruments. Include preparation, failed filtering/reset, flags,
control, randomness, readout, records, classical work and calibration. Geometric
retry uses the complete attempt cost divided by \(s_Ns^2\), only for genuinely
fresh, independently repeatable preparations. Calibration is separately
amortized over delivered outputs. Unknown inputs are not freely repeatable.

## Evidence and remaining domain

New proofs are analytic, with exact arithmetic and finite floating witnesses;
no new Lean theorem is claimed. All unchanged proof/configuration inputs are
checked against their original 158-entry source identity. The old 13 runtime
inputs and receipts are preserved. New runners record their actual environment,
git checkout and input/output hashes. No real device data have been supplied.

Simultaneous red-plus-blue evolution has an explicit infinite-tail counterexample
and does not inherit the N+2L support claim. Unbounded stopping, generic leakage,
infinite reference, coherent control, bath deletion, full OPT reconstruction,
independent complex selection, QFT/EFT, particle selection and gravity remain
separate responsibilities in the continuous roadmap.

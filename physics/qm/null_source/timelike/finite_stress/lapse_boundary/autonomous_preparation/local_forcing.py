"""Exact S3 pair counts and a compact-test omitted-controller-mode coefficient."""
import sympy as s
from common import finish,require,iv,outward,above
# Exact integer identities check the degeneracy bookkeeping, not ODEs.
for n in range(2,81):
    js=list(range(n-1,0,-2))
    require(sum(j*j for j in js)*6==n*(n*n-1),'full spatial spectral multiplicity')
    for K in [1,2,3,7,20,50]:
        for ell in range(n-1):
            if (n-ell-2)%2:continue
            rr=(n-ell-2)//2
            if rr<0:continue
            direct=sum(1 for j in range(rr+1,rr+ell+2) if j<=K and n-j<=K)
            formula=max(0,min(ell+1,2*K-n+1))
            require(direct==formula,'actual two-field canonical cutoff count')
for n in range(3,81,2):
    jmax=(n-1)//2
    require(8*sum(range(1,jmax+1))==n*n-1,'three-field spectral weight')
V0=2*iv.pi**2
coefficient=iv.exp(-iv.mpf(2)/3)*iv.cos(iv.mpf(1)/2)**2/(1600*V0)
require(above(coefficient,'.0000125'),'strict inhomogeneous first-order coefficient')
finish('local_forcing.py',{
 'V0':'2*pi^2',
 'free_Bell_covariance':'(4*V0)^(-1) sum_r exp[-i*(ell+2+2r)*(t-s)]',
 'actual_pair_count':'max(0,min(ell+1,2*K-n+1))',
 'full_spatial_spectral_weight':'n*(n^2-1)/(24*V0)',
 'time_smeared_free_vector_actual_cutoff_limit':True,
 'all_finite_spatial_Sobolev_moments_for_smooth_compact_time_test':True,
 'conformal_controller_first_Dyson_total_norm_squared':'lambda^2/(64*V0) sum_(odd n>=3) (n^2-1)*abs(g_hat(n))^2',
 'compact_test_half_width':'.1',
 'ell1_per_harmonic_first_order_coefficient_lower_interval':outward(coefficient),
 'coefficient_multiplies':'lambda^2',
 'nonzero_for_every_nonzero_test_claimed':False,
 'controlled_higher_Dyson_remainder_or_exact_interacting_probability_claimed':False,
 'full_interacting_local_Hamiltonian_or_stress_constructed':False
})

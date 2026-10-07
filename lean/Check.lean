import Erdos1070

/-! Run `lake env lean Check.lean` to see the statements, the definitions they use,
and the axioms of the main theorems and of the one external input (OpenAI's `wild_fourier`). -/

#print Erdos1070.UnitFree
#print Erdos1070.indepNum
#print Erdos1070.f
#print Erdos1070.square
#print Erdos1070.upperDensity
#print Erdos1070.m1
#check @Erdos1070.f_div_tendsto_m1
#check @Erdos1070.m1_mul_le_f
#check @OAI.PlaneFiveColor.Spectral.wild_fourier
#print axioms Erdos1070.f_div_tendsto_m1
#print axioms Erdos1070.m1_mul_le_f
#print axioms OAI.PlaneFiveColor.Spectral.wild_fourier

/-! Disc version (erdosproblems.com definition: limsup over real `R → ∞` of `λ(A ∩ B_R)/λ(B_R)`). -/
#print Erdos1070.upperDensityBall
#print Erdos1070.m1Ball
#check @Erdos1070.m1Ball_eq_alphaStar
#check @Erdos1070.m1Ball_eq_m1
#check @Erdos1070.f_div_tendsto_m1Ball
#check @Erdos1070.m1Ball_mul_le_f
#print axioms Erdos1070.f_div_tendsto_m1Ball
#print axioms Erdos1070.m1Ball_mul_le_f

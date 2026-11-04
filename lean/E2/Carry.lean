import E2.Clock
import E2.Weighted
import E2.CantorCarryScalar
import E2.WeightedTransport
import E2.CarryRouting

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Scalar facts preceding Lemma 9.2, including uniform translation constants. -/
theorem cantor_carry_calculus :
    (∀ i, LipschitzWith 2 (cantorTranslation i)) ∧
    LipschitzWith 2 carryFunction ∧
    (∀ i b, cantorTranslation i (cantorCoordinate b) = cantorCoordinate (addBits i b)) ∧
    (∀ b, carryFunction (cantorCoordinate b) = carryOnBits b) ∧
    (∀ a ∈ cantorSet, carryFunction a = 1-digitFunction a +
      (1/4)*digitFunction a*carryFunction (tailFunction a)) ∧
    (∀ a ∈ cantorSet, cantorTranslation 1 a = a-1+(7/4)*carryFunction a) ∧
    (∀ i j a, a ∈ cantorSet → cantorTranslation (i+j) a = cantorTranslation i (cantorTranslation j a)) := by
  exact ⟨cantorTranslation_lipschitz,carryFunction_lipschitz,cantorTranslation_on_bits,
    carryFunction_on_bits,carryFunction_recursion,cantorTranslation_one,cantorTranslation_composition⟩

def AddressApprox {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d) (v h : Mat d) : Prop :=
  ClockApprox s δ c ∧ Domain.unitary.Holds v ∧ Domain.positiveContraction.Holds h ∧
  weighted s (h - ((1-c.P) + (1/4:ℂ) • (c.P*c.T*h*c.T.conjTranspose))) ≤ δ ∧
  weighted s (comm c.P (c.T*h*c.T.conjTranspose)) ≤ δ ∧
  weighted s (comm h c.A) ≤ δ ∧
  weighted s (v.conjTranspose*c.A*v - (c.A-1+(7/4:ℂ) • h)) ≤ δ ∧
  hs (comm v s.xi) ≤ δ ∧ hs (comm h s.xi) ≤ δ

structure AddressRepair {d : ℕ} (c : ClockData d) (s : State d) (v h : Mat d) (δ C : ℝ)
    extends SpectralRepair c s δ C where
  carry : weighted s (h - matrixFunction carryFunction Ahat) ≤ C*δ
  translations : ∀ i, weighted s (translate v.conjTranspose Ahat i -
    matrixFunction (cantorTranslation i) Ahat) ≤ C*(i+1)*δ
  joint_address : ∀ i j (J : Mat d), ‖J‖ ≤ 1 → weighted s (comm J c.A) ≤ δ →
    hs (comm J s.xi) ≤ δ →
    weighted s (comm (translate v J i) (rawDigit c j)) ≤ C*(i+1)*4^j*δ

/-- Lemma 9.2: the carry repair, linear translation loss, and address routing. -/
theorem carry_translation : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : State d)
    (δ : ℝ) (c : ClockData d) (v h : Mat d), 0 ≤ δ → AddressApprox s δ c v h →
    Nonempty (AddressRepair c s v h δ C) := by
  obtain ⟨C₀,hC₀,hrepair⟩ := clock_spectral_repair
  let K := C₀+1
  have hK : 1≤K := by dsimp [K]; linarith
  have hK0 : 0≤K := by linarith
  refine ⟨2048*K,by positivity,?_⟩
  intro d s δ c v h hδ ha
  rcases ha with ⟨hc,hv,hh,hrec,_hcommP,_hcommH,hstep,hσv,_hσh⟩
  obtain ⟨r₀⟩ := hrepair d s δ c hδ hc
  let r : SpectralRepair c s δ K := {
    Ahat := r₀.Ahat
    spectrum := r₀.spectrum
    closeness := r₀.closeness.trans (by dsimp [K]; nlinarith)
    digits := fun j => (r₀.digits j).trans (by gcongr; dsimp [K]; linarith) }
  have hcarry := spectral_repair_carry s δ K c h hδ hK hc hh hrec r
  have hstep' := spectral_repair_carry_step s δ K c v h hδ hK hc hv hσv hstep r hcarry
  have hσA : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have htrans := cantor_translation_linear s δ K r.Ahat v hδ hK r.spectrum hv hσv hσA hstep'
  refine ⟨{
    Ahat := r.Ahat
    spectrum := r.spectrum
    closeness := r.closeness.trans ?_
    digits := ?_
    carry := hcarry.trans ?_
    translations := ?_
    joint_address := ?_ }⟩
  · nlinarith
  · intro j
    exact (r.digits j).trans (by gcongr; nlinarith)
  · nlinarith
  · intro i
    have hi0 : (0:ℝ)≤(i:ℝ) := Nat.cast_nonneg i
    exact (htrans i).trans (by
      calc
        (i:ℝ)*(138*K)*δ = 138*K*(i:ℝ)*δ := by ring
        _ ≤ 2048*K*(i+1)*δ := by gcongr <;> nlinarith [mul_nonneg hK0 hi0])
  · intro i j J hnJ hJA hσJ
    exact spectral_repair_address_routing s δ K c v hδ hK hc hv hσv r htrans i j J hnJ hJA hσJ

end
end E2

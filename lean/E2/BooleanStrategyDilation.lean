import E2.FiniteNaimark
import E2.Game

namespace E2.BooleanStrategyDilation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
open FiniteNaimark
variable {G : BCSGame} {d : ℕ}

abbrev AliceSpace (G : BCSGame) (d : ℕ) := Space (Fin G.numVars → Bool) (Fin d)
abbrev BobSpace (d : ℕ) := Space Bool (Fin d)

def alice (s : Strategy G d) (c : Fin G.contexts) (a : Fin G.numVars → Bool) :
    Matrix (AliceSpace G d) (AliceSpace G d) ℂ :=
  effect (s.alice c) (fun _ => false) a

def bob (s : Strategy G d) (v : Fin G.numVars) (b : Bool) :
    Matrix (BobSpace d) (BobSpace d) ℂ := effect (s.bob v) false b

def jointEmbedding (G : BCSGame) (d : ℕ) :
    Matrix (AliceSpace G d × BobSpace d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker embedding embedding

def rho (s : Strategy G d) :
    Matrix (AliceSpace G d × BobSpace d) (AliceSpace G d × BobSpace d) ℂ :=
  jointEmbedding G d * s.rho * (jointEmbedding G d).conjTranspose

theorem jointEmbedding_isometry (G : BCSGame) (d : ℕ) :
    (jointEmbedding G d).conjTranspose * jointEmbedding G d = 1 := by
  unfold jointEmbedding
  erw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul]
  rw [embedding_isometry,embedding_isometry,Matrix.one_kronecker_one]

theorem rho_positive (s : Strategy G d) : (rho s).PosSemidef :=
  s.rho_positive.mul_mul_conjTranspose_same _

theorem rho_trace (s : Strategy G d) : Matrix.trace (rho s) = 1 := by
  rw [rho,Matrix.trace_mul_cycle,jointEmbedding_isometry,Matrix.one_mul,s.rho_trace]

theorem alice_hermitian (s : Strategy G d) (c a) : (alice s c a).conjTranspose = alice s c a :=
  effect_hermitian _ _ _

theorem alice_mul (s : Strategy G d) (c a b) :
    alice s c a * alice s c b = if a = b then alice s c a else 0 :=
  effect_mul _ (s.alice_positive c) (s.alice_complete c) _ _ _

theorem alice_sum (s : Strategy G d) (c) : (∑ a, alice s c a) = 1 :=
  effect_sum _ (s.alice_positive c) (s.alice_complete c) _

theorem bob_hermitian (s : Strategy G d) (v b) : (bob s v b).conjTranspose = bob s v b :=
  effect_hermitian _ _ _

theorem bob_mul (s : Strategy G d) (v a b) :
    bob s v a * bob s v b = if a = b then bob s v a else 0 :=
  effect_mul _ (s.bob_positive v) (s.bob_complete v) _ _ _

theorem bob_sum (s : Strategy G d) (v) : (∑ b, bob s v b) = 1 :=
  effect_sum _ (s.bob_positive v) (s.bob_complete v) _

theorem alice_compression (s : Strategy G d) (c a) :
    (embedding (o := Fin G.numVars → Bool) (b := Fin d)).conjTranspose *
      alice s c a * embedding = s.alice c a := effect_compression _ (s.alice_positive c) _ _

theorem bob_compression (s : Strategy G d) (v b) :
    (embedding (o := Bool) (b := Fin d)).conjTranspose *
      bob s v b * embedding = s.bob v b := effect_compression _ (s.bob_positive v) _ _

/-- Every original mixed-state correlation is preserved exactly. -/
theorem correlation (s : Strategy G d) (c a v b) :
    Matrix.trace (rho s * Matrix.kronecker (alice s c a) (bob s v b)) =
      Matrix.trace (s.rho * Matrix.kronecker (s.alice c a) (s.bob v b)) := by
  have he : (jointEmbedding G d).conjTranspose *
      Matrix.kronecker (alice s c a) (bob s v b) * jointEmbedding G d =
      Matrix.kronecker (s.alice c a) (s.bob v b) := by
    unfold jointEmbedding
    erw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
    rw [alice_compression,bob_compression]
    rfl
  calc
    _ = Matrix.trace (s.rho * ((jointEmbedding G d).conjTranspose *
        Matrix.kronecker (alice s c a) (bob s v b) * jointEmbedding G d)) := by
      change Matrix.trace ((jointEmbedding G d * s.rho * (jointEmbedding G d).conjTranspose) *
        Matrix.kronecker (alice s c a) (bob s v b)) = _
      calc
        _ = Matrix.trace ((jointEmbedding G d * s.rho) *
            ((jointEmbedding G d).conjTranspose * Matrix.kronecker (alice s c a) (bob s v b))) := by
          simp only [Matrix.mul_assoc]
        _ = Matrix.trace (((jointEmbedding G d).conjTranspose *
            Matrix.kronecker (alice s c a) (bob s v b)) * (jointEmbedding G d * s.rho)) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((((jointEmbedding G d).conjTranspose *
            Matrix.kronecker (alice s c a) (bob s v b)) * jointEmbedding G d) * s.rho) := by
          simp only [Matrix.mul_assoc]
        _ = _ := Matrix.trace_mul_comm _ _
    _ = _ := by rw [he]

/-- Bob's common dilation costs exactly a factor of three. -/
theorem bob_dimension (d : ℕ) : Fintype.card (BobSpace d) = 3*d := by
  simp only [BobSpace,Space,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  omega

theorem alice_dimension (G : BCSGame) (d : ℕ) :
    Fintype.card (AliceSpace G d) = (1+2^G.numVars)*d := by
  simp [AliceSpace,Space,Fintype.card_fun,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,Fintype.card_fin]
  ring

end
end E2.BooleanStrategyDilation

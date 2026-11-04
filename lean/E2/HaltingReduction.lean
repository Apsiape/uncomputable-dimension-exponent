import E2.EffectiveOracle
import E2.SeparatedDigits

namespace E2.HaltingReduction
noncomputable section
set_option maxHeartbeats 300000
open Encodable EffectiveCoding SeparatedDigits
attribute [local instance] Classical.propDecidable

variable {O : Set (ℕ →. ℕ)}

theorem total_comp {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) :=
  (hf.comp hg).of_eq (fun n => Part.bind_some (g n) _)

theorem total_pair {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  refine (hf.pair hg).of_eq ?_
  intro n
  apply Part.ext'
  · simp [Seq.seq, Part.bind, Part.assert, Part.map, Part.some]
  · intros; rfl

theorem total_computable {f : ℕ → ℕ} (hf : Computable f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

theorem total_rec (a : ℕ) (s : ℕ → ℕ → ℕ)
    (hs : Nat.RecursiveIn O (fun n => Part.some (s n.unpair.1 n.unpair.2))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.rec a s n)) := by
  have hstep := total_comp hs
    (total_computable (Computable.snd.comp Computable.unpair))
  have hbase := total_computable (O := O) (Computable.const a : Computable (fun _ : ℕ => a))
  have hrec := hbase.prec hstep
  have he (n : ℕ) :
      n.rec (Part.some a) (fun y ih => ih >>= fun i => Part.some (s y i)) =
      Part.some (Nat.rec a s n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Nat.rec_add_one, ih]
      exact Part.bind_some (Nat.rec a s n : ℕ) (fun i => Part.some (s n i))
  have hr : Nat.RecursiveIn O (fun p => Part.some (Nat.rec a s p.unpair.2)) := by
    refine hrec.of_eq ?_
    intro p
    cases hx : Nat.unpair p with
    | mk b n => simpa only [hx,Nat.unpair_pair] using he n
  have hi : Computable (fun n : ℕ => Nat.pair 0 n) :=
    Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id
  exact (total_comp hr (total_computable hi)).of_eq (fun n => by simp)

def digitQuery (e m : ℕ) : ℕ :=
  encode (((4*(m:ℚ)+2/3) / (4:ℚ)^(e+1)))

theorem digitQuery_computable : Computable (fun n : ℕ => digitQuery n.unpair.1 n.unpair.2) := by
  have hp : Primrec (fun e : ℕ => 4^(e+1)) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow |>.comp (Primrec.const 4) Primrec.succ
  have hdiv : Computable (fun e : ℕ => (1:ℚ)/(4:ℚ)^(e+1)) := by
    refine (rat_divNat.comp ((Computable.const 1).pair hp.to_comp)).of_eq ?_
    intro e
    push_cast
    rfl
  have he := Computable.fst.comp Computable.unpair
  have hm := Computable.snd.comp Computable.unpair
  refine (Computable.encode.comp
    (rat_mul.comp (rat_add.comp (rat_mul.comp (Computable.const 4)
      (rat_natCast.comp hm)) (Computable.const (2/3))) (hdiv.comp he))).of_eq ?_
  intro n
  dsimp [digitQuery]
  rw [mul_one_div]

theorem query_digit (A : Set ℕ) (e : ℕ) :
    (if (rationalCode (digitQuery e (digitPrefix A e)) : ℝ) < value A then 1 else 0) = bit A e := by
  have h := scaled_bounds A (e+1)
  simp only [digitPrefix, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  have hp : (0:ℝ) < 4^(e+1) := by positivity
  rw [digitQuery,rational_encode]
  push_cast
  simp only [div_lt_iff₀ hp]
  unfold bit at *
  by_cases hh : e ∈ A
  · simp only [hh,ite_true,Nat.cast_one] at h ⊢
    split_ifs <;> linarith
  · simp only [hh,ite_false,Nat.cast_zero] at h ⊢
    split_ifs <;> linarith

theorem halting_reducible_to_theta : TuringReducible haltingOracle (realOracle thetaK) := by
  let b : ℕ → ℕ := fun n => if (rationalCode n : ℝ) < thetaK then 1 else 0
  have hb : Nat.RecursiveIn {realOracle thetaK} (fun n => Part.some (b n)) := by
    change Nat.RecursiveIn {realOracle thetaK} (realOracle thetaK)
    exact .oracle _ (by simp)
  let step : ℕ → ℕ → ℕ := fun e m => 4*m+b (digitQuery e m)
  have hs : Nat.RecursiveIn {realOracle thetaK} (fun n => Part.some (step n.unpair.1 n.unpair.2)) := by
    have hmul : Computable (fun n : ℕ => 4*n.unpair.2) :=
      Primrec.nat_mul.to_comp.comp (Computable.const 4) (Computable.snd.comp Computable.unpair)
    have hadd : Computable (fun n : ℕ => n.unpair.1+n.unpair.2) :=
      Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.unpair)
        (Computable.snd.comp Computable.unpair)
    exact (total_comp (total_computable hadd)
      (total_pair (total_computable hmul) (total_comp hb (total_computable digitQuery_computable)))).of_eq
        (fun n => by simp only [Nat.unpair_pair,step])
  have hr := total_rec 0 step hs
  have he : ∀ n, Nat.rec 0 step n = digitPrefix haltingSet n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Nat.rec_add_one,step,ih,digitPrefix]
      congr 1
      simpa only [b,theta_value] using query_digit haltingSet n
  have hpref : Nat.RecursiveIn {realOracle thetaK} (fun n => Part.some (digitPrefix haltingSet n)) :=
    hr.of_eq (fun n => congrArg Part.some (he n))
  have harg := total_pair (total_computable (Computable.id : Computable (fun n : ℕ => n))) hpref
  have hd := total_comp hb (total_comp (total_computable digitQuery_computable) harg)
  apply RecursiveIn.iff_nat.mpr
  refine hd.of_eq ?_
  intro n
  simp only [Nat.unpair_pair,id_eq,haltingOracle,b,theta_value]
  exact congrArg Part.some (query_digit haltingSet n)

end
end E2.HaltingReduction

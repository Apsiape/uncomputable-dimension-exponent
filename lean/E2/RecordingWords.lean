import E2.RecordingNorms

namespace E2.Recording
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

abbrev Record {m : ℕ} (o : Fin m → ℕ) := ∀ i, Fin (o i)

def word {d m : ℕ} {o : Fin m → ℕ} (P : ∀ i, Fin (o i) → Mat d) (a : Record o) : Mat d :=
  (List.ofFn (fun i => P i (a i))).reverse.prod

theorem sum_records_cons {m : ℕ} (o : Fin (m+1) → ℕ) {A : Type*} [AddCommMonoid A]
    (f : Record o → A) : (∑ a, f a)=∑ b : Fin (o 0), ∑ a : Record (fun i => o i.succ), f (Fin.cons b a) := by
  calc
    _=∑ t : Fin (o 0) × Record (fun i => o i.succ), f (Fin.cons t.1 t.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun i => Fin (o i))) _ _ (fun _ => rfl)).symm
    _=_ := Fintype.sum_prod_type _

theorem word_cons {d m : ℕ} {o : Fin (m+1) → ℕ}
    (P : ∀ i, Fin (o i) → Mat d) (b : Fin (o 0)) (a : Record (fun i => o i.succ)) :
    word P (Fin.cons b a)=word (fun i => P i.succ) a*P 0 b := by
  simp only [word,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,List.reverse_cons,List.prod_append,List.prod_singleton]

theorem record_complete {d m : ℕ} {o : Fin m → ℕ} (P : ∀ i, Fin (o i) → Mat d)
    (hP : ∀ i, ∑ a, (P i a).conjTranspose*P i a=1) :
    (∑ a : Record o, (word P a).conjTranspose*word P a)=1 := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
    rw [sum_records_cons]
    simp only [word_cons,Matrix.conjTranspose_mul]
    have hi := ih (fun i => P i.succ) (fun i => hP i.succ)
    have he (b : Fin (o 0)) :
        (∑ a : Record (fun i => o i.succ), (P 0 b).conjTranspose*(word (fun i => P i.succ) a).conjTranspose*
          (word (fun i => P i.succ) a*P 0 b))=(P 0 b).conjTranspose*P 0 b := by
      calc
        _=(P 0 b).conjTranspose*(∑ a : Record (fun i => o i.succ),
            (word (fun i => P i.succ) a).conjTranspose*word (fun i => P i.succ) a)*P 0 b := by
          simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
        _=_ := by rw [hi,Matrix.mul_one]
    simp_rw [he]
    exact hP 0

theorem record_coComplete {d m : ℕ} {o : Fin m → ℕ} (P : ∀ i, Fin (o i) → Mat d)
    (hP : ∀ i, ∑ a, P i a*(P i a).conjTranspose=1) :
    (∑ a : Record o, word P a*(word P a).conjTranspose)=1 := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
    rw [sum_records_cons,Finset.sum_comm]
    simp only [word_cons,Matrix.conjTranspose_mul]
    have he (a : Record (fun i => o i.succ)) :
        (∑ b : Fin (o 0), word (fun i => P i.succ) a*P 0 b*
          ((P 0 b).conjTranspose*(word (fun i => P i.succ) a).conjTranspose))=
        word (fun i => P i.succ) a*(word (fun i => P i.succ) a).conjTranspose := by
      calc
        _=word (fun i => P i.succ) a*(∑ b, P 0 b*(P 0 b).conjTranspose)*
            (word (fun i => P i.succ) a).conjTranspose := by
          simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
        _=_ := by rw [hP,Matrix.mul_one]
    simp_rw [he]
    exact ih (fun i => P i.succ) (fun i => hP i.succ)

theorem composition_commutator {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (P : ι → Mat d) (K : κ → Mat d) (X : Mat d)
    (hP : ∑ i, (P i).conjTranspose*P i=1) (hK : ∑ j, K j*(K j).conjTranspose=1) :
    familyNorm (fun t : ι × κ => comm (P t.1*K t.2) X)≤
      familyNorm (fun j => comm (K j) X)+familyNorm (fun i => comm (P i) X) := by
  have he : (fun t : ι × κ => comm (P t.1*K t.2) X)=
      (fun t => P t.1*comm (K t.2) X+comm (P t.1) X*K t.2) := by
    funext t
    simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    abel
  rw [he]
  exact (familyNorm_add _ _).trans_eq (by
    rw [familyNorm_pair_left P hP (fun j => comm (K j) X),
      familyNorm_pair_right K hK (fun i => comm (P i) X)])

theorem record_commutator {d m : ℕ} {o : Fin m → ℕ} (P : ∀ i, Fin (o i) → Mat d)
    (hP : ∀ i, ∑ a, (P i a).conjTranspose*P i a=1)
    (hPc : ∀ i, ∑ a, P i a*(P i a).conjTranspose=1) (X : Mat d) :
    familyNorm (fun a : Record o => comm (word P a) X)≤
      ∑ i, familyNorm (fun a => comm (P i a) X) := by
  induction m with
  | zero => simp [word,comm,Companion.Analytic.comm,familyNorm,stack,hsNorm,hsSquared]
  | succ m ih =>
    have he := familyNorm_equiv (Fin.consEquiv (fun i => Fin (o i)))
      (fun a => comm (word P a) X)
    rw [←he]
    change familyNorm (fun t : Fin (o 0) × Record (fun i => o i.succ) =>
      comm (word P (Fin.cons t.1 t.2)) X)≤_
    simp only [word_cons]
    have hswap := familyNorm_equiv (Equiv.prodComm (Fin (o 0)) (Record (fun i => o i.succ)))
      (fun t : Record (fun i => o i.succ) × Fin (o 0) => comm (word (fun i => P i.succ) t.1*P 0 t.2) X)
    change familyNorm (fun t : Fin (o 0) × Record (fun i => o i.succ) =>
        comm (word (fun i => P i.succ) t.2*P 0 t.1) X)=
      familyNorm (fun t : Record (fun i => o i.succ) × Fin (o 0) =>
        comm (word (fun i => P i.succ) t.1*P 0 t.2) X) at hswap
    rw [hswap]
    have h := composition_commutator (word (fun i => P i.succ)) (P 0) X
      (record_complete _ (fun i => hP i.succ)) (hPc 0)
    have hi := ih (fun i => P i.succ) (fun i => hP i.succ) (fun i => hPc i.succ)
    rw [Fin.sum_univ_succ]
    linarith

end
end E2.Recording

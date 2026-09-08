/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# Gauss sums for Dirichlet characters
-/

public section
variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

open AddChar DirichletCharacter

/-
**gaussSum_aux_of_mulShift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gaussSum_aux_of_mulShift (χ : DirichletCharacter R N) {d : Nat} (hd : d ∣ 
N) (he : e.mulShift d = 1) {u : (ZMod N)ˣ} (hu : ZMod.unitsMap hd u = 1) : χ u *
 gaussSum χ e = gaussSum χ e
参数：χ : DirichletCharacter R N；hd : d ∣ N；he : e.mulShift d = 1；ZMod N；hu : ZMod.
unitsMap hd u = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `AddChar.mulShift_mul`：mulShift_mul (ψ : AddChar R M) (r s : R) : mulShif
t ψ r * mulShift ψ s = mulShift ψ (r + s)
· 使用引理 `AddChar.mulShift_one`：mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ
· 使用定理 `mul_eq_right`：mul_eq_right : a * b = b ↔ a = 1
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `ZMod.intCast_cast`：intCast_cast (i : ZMod n) : ((cast i : Int) : R) = ca
st i
（共 54 条，此处仅展示前 30 条）
-/
lemma gaussSum_aux_of_mulShift (χ : DirichletCharacter R N) {d : ℕ}
    (hd : d ∣ N) (he : e.mulShift d = 1) {u : (ZMod N)ˣ} (hu : ZMod.unitsMap hd u = 1) :
    χ u * gaussSum χ e = gaussSum χ e := by
  suffices e.mulShift u = e by conv_lhs => rw [← this, gaussSum_mulShift]
  rw [(by ring : u.val = (u - 1) + 1), ← mulShift_mul, mulShift_one, mul_eq_right]
  rsuffices ⟨a, ha⟩ : (d : ℤ) ∣ (u.val.val - 1 : ℤ)
  · have : u.val - 1 = ↑(u.val.val - 1 : ℤ) := by simp only [ZMod.natCast_val, Int.cast_sub,
      ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_one]
    rw [this, ha]
    ext1 y
    simpa only [Int.cast_mul, Int.cast_natCast, mulShift_apply, mul_assoc, one_apply]
      using DFunLike.ext_iff.mp he (a * y)
  rw [← Units.val_inj, Units.val_one, ZMod.unitsMap_def, Units.coe_map] at hu
  have : ZMod.castHom hd (ZMod d) u.val = ((u.val.val : ℤ) : ZMod d) := by simp
  rwa [MonoidHom.coe_coe, this, ← Int.cast_one, eq_comm,
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hu

/-- If `gaussSum χ e ≠ 0`, and `d` is such that `e.mulShift d = 1`, then `χ` must factor through
`d`. (This will be used to show that Gauss sums vanish when `χ` is primitive and `e` is not.) -/
/-
**factorsThrough_of_gaussSum_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：factorsThrough_of_gaussSum_ne_zero [IsDomain R] {χ : DirichletCharacter R 
N} {d : Nat} (hd : d ∣ N) (he : e.mulShift d = 1) (h_ne : gaussSum χ e != 0) : χ
.FactorsThrough d
参数：hd : d ∣ N；he : e.mulShift d = 1；h_ne : gaussSum χ e != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.factorsThrough_iff_ker_unitsMap`：factorsThrough_iff_k
er_unitsMap {d : Nat} [NeZero n] (hd : d ∣ n) : FactorsThrough χ d ↔ (ZMod.units
Map hd).ker <= χ.toUnitHom.ker
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `gaussSum_aux_of_mulShift`：gaussSum_aux_of_mulShift (χ : DirichletCharact
er R N) {d : Nat} (hd : d ∣ N) (he : e.mulShift d = 1) {u : (ZMod N)ˣ} (hu : ZMo
d.unitsMap hd …

--- 原说明 ---
If `gaussSum χ e ≠ 0`, and `d` is such that `e.mulShift d = 1`, then `χ` must fa
ctor through
`d`. (This will be used to show that Gauss sums vanish when `χ` is primitive and
 `e` is not.)
-/
lemma factorsThrough_of_gaussSum_ne_zero [IsDomain R] {χ : DirichletCharacter R N} {d : ℕ}
    (hd : d ∣ N) (he : e.mulShift d = 1) (h_ne : gaussSum χ e ≠ 0) :
    χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro _ hu
  simpa [← Units.val_inj, h_ne] using gaussSum_aux_of_mulShift e χ hd he hu

/-- If `χ` is primitive, but `e` is not, then `gaussSum χ e = 0`. -/
/-
**gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive [IsDomain R] {χ : Diric
hletCharacter R N} (hχ : IsPrimitive χ) (he : ¬IsPrimitive e) : gaussSum χ e = 0
参数：hχ : IsPrimitive χ；he : ¬IsPrimitive e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `AddChar.exists_divisor_of_not_isPrimitive`：exists_divisor_of_not_isPrimi
tive (he : ¬e.IsPrimitive) : exists d : Nat, d ∣ N ∧ d < N ∧ e.mulShift d = 1
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用引理 `factorsThrough_of_gaussSum_ne_zero`：factorsThrough_of_gaussSum_ne_zero [
IsDomain R] {χ : DirichletCharacter R N} {d : Nat} (hd : d ∣ N) (he : e.mulShift
 d = 1) (h_ne : gaussSum…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
If `χ` is primitive, but `e` is not, then `gaussSum χ e = 0`.
-/
lemma gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive [IsDomain R]
    {χ : DirichletCharacter R N} (hχ : IsPrimitive χ) (he : ¬IsPrimitive e) :
    gaussSum χ e = 0 := by
  contrapose! hχ
  rcases e.exists_divisor_of_not_isPrimitive he with ⟨d, hd₁, hd₂, hed⟩
  have : χ.conductor ≤ d := Nat.sInf_le <| factorsThrough_of_gaussSum_ne_zero e hd₁ hed hχ
  exact (this.trans_lt hd₂).ne

/-- If `χ` is a primitive character, then the function `a ↦ gaussSum χ (e.mulShift a)`, for any
fixed additive character `e`, is a constant multiple of `χ⁻¹`. -/
/-
**gaussSum_mulShift_of_isPrimitive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gaussSum_mulShift_of_isPrimitive [IsDomain R] {χ : DirichletCharacter R N}
 (hχ : IsPrimitive χ) (a : ZMod N) : gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSu
m χ e
参数：hχ : IsPrimitive χ；a : ZMod N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gaussSum_mulShift_eq`：gaussSum_mulShift_eq (χ : MulChar R R') (ψ : AddCh
ar R R') (a : Rˣ) : gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive`：gaussSum_eq_zero_of_
isPrimitive_of_not_isPrimitive [IsDomain R] {χ : DirichletCharacter R N} (hχ : I
sPrimitive χ) (he : ¬IsPrimitive e) : ga…
· 使用引理 `AddChar.not_isPrimitive_mulShift`：not_isPrimitive_mulShift [Finite R] (e
 : AddChar R R') {r : R} (hr : ¬ IsUnit r) : ¬ IsPrimitive (e.mulShift r)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `χ` is a primitive character, then the function `a ↦ gaussSum χ (e.mulShift a
)`, for any
fixed additive character `e`, is a constant multiple of `χ⁻¹`.
-/
lemma gaussSum_mulShift_of_isPrimitive [IsDomain R] {χ : DirichletCharacter R N}
    (hχ : IsPrimitive χ) (a : ZMod N) :
    gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSum χ e := by
  by_cases ha : IsUnit a
  · simpa [ha.unit_spec] using gaussSum_mulShift_eq χ e ha.unit
  · rw [MulChar.map_nonunit _ ha, zero_mul]
    exact gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive _ hχ (not_isPrimitive_mulShift e ha)

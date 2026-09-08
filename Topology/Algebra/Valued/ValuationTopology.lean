/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Order.GroupWithZero.Range

/-!
# The topology on a valued ring

In this file, we define the non-Archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.

*NOTE* (2025-07-02):
The `Valued` class defined in this file will eventually get replaced with `ValuativeRel`
from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`. New developments on valued rings/fields
should take this into consideration.

-/

@[expose] public section

open scoped Topology uniformity
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Set Valuation

noncomputable section

universe v u

variable {R K : Type u} [Ring R] [DivisionRing K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

/-
**Valuation.map_eq_one_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：map_eq_one_of_forall_lt [MulArchimedean Γ₀] {v : Valuation K Γ₀} {r : Γ₀} 
(hr : r != 0) (h : forall x : K, v x != 0 -> r < v x) (x : K) (hx : v x != 0) : 
v x = 1
参数：hr : r != 0；h : forall x : K, v x != 0 -> r < v x；x : K；hx : v x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `exists_pow_lt`：exists_pow_lt {a : R} (ha : a < 1) (b : R) : exists n : N
at, a ^ n < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_lt_one'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, a⁻¹ < 1 ↔ 1 < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
-/
lemma map_eq_one_of_forall_lt [MulArchimedean Γ₀] {v : Valuation K Γ₀} {r : Γ₀} (hr : r ≠ 0)
    (h : ∀ x : K, v x ≠ 0 → r < v x) (x : K) (hx : v x ≠ 0) : v x = 1 := by
  lift r to Γ₀ˣ using IsUnit.mk0 _ hr
  rcases lt_trichotomy (Units.mk0 _ hx) 1 with H | H | H
  · obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ k) (by simp [hx])
    simp [← Units.val_lt_val, ← map_pow, h.not_gt] at hk
  · simpa [Units.ext_iff] using H
  · rw [← inv_lt_one'] at H
    obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ (-k : ℤ)) (by simp [hx])
    simp only [zpow_neg, zpow_natCast, map_inv₀, map_pow] at h
    simp [← Units.val_lt_val, h.not_gt, inv_pow] at hk

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
/-
**Valuation.subgroups_basis** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：subgroups_basis : RingSubgroupsBasis fun γ : (ValueGroup₀ (.ofClass v))ˣ =
> v.ltAddSubgroup Units.map (ValueGroup₀.embedding (f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Monotone.map_inf`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (min x y) = 
f x ⊓ …
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Units.min_val`：min_val [Monoid α] [LinearOrder α] (a b : αˣ) : (min a b)
.val = min a.val b.val
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubgroup.mk.congr_simp`：∀ {G : Type u_3} [inst : AddGroup G] (toAddSu
bmonoid toAddSubmonoid_1 : AddSubmonoid G)   (e_toAddSubmonoid : toAddSubmonoid 
= toAddSubmonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `exists_square_le`：exists_square_le [MulLeftStrictMono α] (a : α) : exist
s b : α, b * b <= a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.instIsOrderedMonoid`：∀ {A : Type u_1} {B :
 Type u_2} [inst : MonoidWithZero A] [inst_1 : LinearOrderedCommGroupWithZero B]
 {f : A →*₀ B},   IsOrderedMonoid f.Val…
· 使用定理 `Valuation.coe_ltAddSubgroup`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ri
ng R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   (γ : Γ
₀ˣ), ↑(v.ltAddSub…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `mul_lt_mul''`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b c d : α} [in
st_1 : Preorder α] [PosMulStrictMono α] [MulPosMono α],   a < b → c < d → 0 ≤ a 
→ …
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
The basis of open subgroups for the topology on a ring determined by a valuation
.
-/
theorem subgroups_basis :
    RingSubgroupsBasis fun γ : (ValueGroup₀ (.ofClass v))ˣ ↦
      v.ltAddSubgroup <| Units.map (ValueGroup₀.embedding (f := (.ofClass v))) γ :=
  { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      have hmin : embedding (min γ₀.1 γ₁.1) = min (embedding γ₀.1) (embedding γ₁.1) :=
        embedding_strictMono.monotone.map_inf γ₀.1 γ₁.1
      simp [ltAddSubgroup, hmin]
      tauto
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, AddSubgroup.coe_set_mk,
        AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, mem_ofPred_eq] at r_in s_in
      simp only [coe_ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, mem_ofPred_eq]
      rw [← restrict_lt_iff_lt_embedding] at *
      calc
        v.restrict (r * s) = v.restrict r * v.restrict s := Valuation.map_mul _ _ _
        _ < γ₀.1 * γ₀.1 := by gcongr <;> exact zero_le
        _ ≤ γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : (ValueGroup₀ (.ofClass v))ˣ)
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul, Hx, zero_mul]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by
          simp [restrict₀_apply, embedding_apply, hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm, map_mul, hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx,
          mul_zero, Units.zero_lt]
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by simp [restrict₀_apply, embedding_apply,
          hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm, map_mul, hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `Valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `IsUniformAddGroup`. -/
/-
**Valued** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Ring R] → (Γ₀ : outParam (Type v)) → [LinearOrderedCommGro
upWithZero Γ₀] → Type (max u v)
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valued ring is a ring that comes equipped with a distinguished valuation. The 
class `Valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a t
ype belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `UniformSpace`, `IsUniformAdd
Group`.
-/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, IsUniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ, { x : R | v.restrict x < γ.1 } ⊆ s

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
@[instance_reducible]
/-
**Valued.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：mk' (v : Valuation R Γ₀) : Valued R Γ₀
参数：v : Valuation R Γ₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f

--- 原说明 ---
Alternative `Valued` constructor for use when there is no preferred `UniformSpac
e` structure.
-/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      let := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp_rw [restrict_lt_iff_lt_embedding]
      exact exists_congr fun γ ↦ by rw [true_and]; rfl }

variable (R Γ₀)
variable [_i : Valued R Γ₀]
/-
**Valued.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : (MonoidW
ithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v.restrict x < γ.1 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ ↦ { x | v.restrict x < γ.1 } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]

open Uniformity in
/-
**Valued.hasBasis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True) fun γ : (MonoidWithZe
roHom.ValueGroup₀ (.ofClass _i.v))ˣ => { p : R × R | v.restrict (p.2 - p.1) < γ.
1 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_zero`：∀ (Gᵣ : Type u_3) [inst : UniformSpace Gᵣ
] [inst_1 : AddGroup Gᵣ] [IsRightUniformAddGroup Gᵣ],   uniformity Gᵣ = Filter.c
omap (fun x => x.2 …
· 使用定理 `IsUniformAddGroup.isRightUniformAddGroup`：∀ (α : Type u_1) [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsRightUniformAddGroup α
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Valued.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fu
n _ => True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v
.restrict x < γ…
-/
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ ↦ True)
    fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ ↦
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _
/-
**Valued.toUniformSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：toUniformSpace_eq : toUniformSpace = @IsTopologicalAddGroup.rightUniformSp
ace R _ v.subgroups_basis.topology _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `Valued.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 R).HasBasis (fun _ 
=> True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { p : R × R
 | v.restrict (p…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Valuation.coe_ltAddSubgroup`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ri
ng R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   (γ : Γ
₀ˣ), ↑(v.ltAddSub…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `RingSubgroupsBasis.hasBasis_nhds_zero`：hasBasis_nhds_zero : HasBasis (@n
hds A hB.topology 0) (fun _ => True) fun i => B i
-/
theorem toUniformSpace_eq : toUniformSpace =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext ((hasBasis_uniformity R Γ₀).eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp_rw [restrict_lt_iff_lt_embedding, sub_eq_add_neg]
  simp

variable {R Γ₀}
/-
**Valued.mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (MonoidWithZeroHom.Va
lueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.1 } subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_translation_add_neg`：∀ {G : Type w} [inst : TopologicalSpace G] [in
st_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.comap (fun x_1 =>
 x_1 + -x) (nh…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Valued.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fu
n _ => True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v
.restrict x < γ…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ,
    { y | (v.restrict (y - x) ) < γ.1 } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_ofPred_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y ↦ y - x).mem_iff]
/-
**Valued.mem_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：mem_nhds_zero {s : Set R} : s in 𝓝 (0 : R) ↔ exists γ : (MonoidWithZeroHom
.ValueGroup₀ (.ofClass _i.v))ˣ, { x | v.restrict x < γ.1 } subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { x | v.restrict x < γ.1 } ⊆ s := by
  simp only [mem_nhds, sub_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-- The set `{ y : R | v y = v x }` is a neighbourhood of `x`.
This does not imply that `v` is locally constant everywhere (since `v ⁻¹' {0}` is not open),
but it is equivalent to the restriction of `v` to the complement of its support being
locally constant. -/
/-
**Valued.locally_const** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：locally_const {x : R} (h : (v x : Γ₀) != 0) : { y : R | v y = v x } in 𝓝 x
参数：h : (v x : Γ₀) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valued.mem_nhds`：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (M
onoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.
1 } s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `Valuation.map_eq_of_sub_lt`：map_eq_of_sub_lt (h : v (y - x) < v x) : v y
 = v x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Valuation.restrict_lt_iff`：restrict_lt_iff {x y : R} : v.restrict x < v.
restrict y ↔ v x < v y

--- 原说明 ---
The set `{ y : R | v y = v x }` is a neighbourhood of `x`.
This does not imply that `v` is locally constant everywhere (since `v ⁻¹' {0}` i
s not open),
but it is equivalent to the restriction of `v` to the complement of its support 
being
locally constant.
-/
theorem locally_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  have h' : v.restrict x ≠ 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)
/-
**Valued.** 是 Mathlib 中的一个实例，位于命名空间 `Valued`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

section Discrete

/-
**Valued.discreteTopology_of_forall_map_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued
`。
形式化陈述：discreteTopology_of_forall_map_eq_one (h : forall x : R, x != 0 -> v x = 1
) : DiscreteTopology R
参数：h : forall x : R, x != 0 -> v x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Valued.instIsTopologicalRing`：∀ {R : Type u} [inst : Ring R] {Γ₀ : Type 
v} [inst_1 : LinearOrderedCommGroupWithZero Γ₀] [_i : Valued R Γ₀],   IsTopologi
calRing R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
-/
lemma discreteTopology_of_forall_map_eq_one (h : ∀ x : R, x ≠ 0 → v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, mem_nhds_zero, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding, Units.val_one, map_one] at hx
  exact ⟨x, hx', hx.ne⟩
/-
**Valued.discreteTopology_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：discreteTopology_of_forall_lt [MulArchimedean Γ₀] [Valued K Γ₀] {r : Γ₀} (
hr : r != 0) (h : forall x : K, v x != 0 -> r < v x) : DiscreteTopology K
参数：hr : r != 0；h : forall x : K, v x != 0 -> r < v x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valued.discreteTopology_of_forall_map_eq_one`：discreteTopology_of_forall
_map_eq_one (h : forall x : R, x != 0 -> v x = 1) : DiscreteTopology R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.map_eq_one_of_forall_lt`：map_eq_one_of_forall_lt [MulArchimede
an Γ₀] {v : Valuation K Γ₀} {r : Γ₀} (hr : r != 0) (h : forall x : K, v x != 0 -
> r < v x) (x : K) (hx …
-/
lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] [Valued K Γ₀] {r : Γ₀} (hr : r ≠ 0)
    (h : ∀ x : K, v x ≠ 0 → r < v x) :
    DiscreteTopology K :=
  discreteTopology_of_forall_map_eq_one (by simpa using Valued.v.map_eq_one_of_forall_lt hr h)

end Discrete

/-
**Valued.cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：cauchy_iff {F : Filter R} : Cauchy F ↔ F.NeBot ∧ forall γ : (MonoidWithZer
oHom.ValueGroup₀ (.ofClass _i.v))ˣ, exists M in F, forallᵉ (x in M) (y in M), _i
.v.restrict (y - x) < γ.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valued.toUniformSpace_eq`：toUniformSpace_eq : toUniformSpace = @IsTopolo
gicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
· 使用定理 `AddGroupFilterBasis.cauchy_iff`：cauchy_iff {F : Filter G} : @Cauchy G B.
uniformSpace F ↔ F.NeBot ∧ forall U in B, exists M in F, forallᵉ (x in M) (y in 
M), y - x in U
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingSubgroupsBasis.mem_addGroupFilterBasis_iff`：mem_addGroupFilterBasis_
iff {V : Set A} : V in hB.toRingFilterBasis.toAddGroupFilterBasis ↔ exists i, V 
= B i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingSubgroupsBasis.mem_addGroupFilterBasis`：mem_addGroupFilterBasis (i) 
: (B i : Set A) in hB.toRingFilterBasis.toAddGroupFilterBasis
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ,
      ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), _i.v.restrict (y - x) < γ.1 := by
  rw [toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

variable (R)

/-- An open ball centred at the origin in a valued ring is open. -/
/-
**Valued.isOpen_ball** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isOpen_ball (r : ValueGroup₀ (.ofClass _i.v)) : IsOpen {x | v.restrict x <
 r}
参数：r : ValueGroup₀ (.ofClass _i.v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valued.mem_nhds`：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (M
onoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.
1 } s…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
An open ball centred at the origin in a valued ring is open.
-/
theorem isOpen_ball (r : ValueGroup₀ (.ofClass _i.v)) :
    IsOpen {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy ↦ (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

/-- An open ball centred at the origin in a valued ring is closed. -/
/-
**Valued.isClosed_ball** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClosed_ball (r : ValueGroup₀ (.ofClass _i.v)) : IsClosed {x | v.restrict
 x < r}
参数：r : ValueGroup₀ (.ofClass _i.v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.isClosed_of_isOpen`：∀ {G : Type u_1} [inst : AddGroup G] [in
st_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (U : AddSubgroup G),   Is
Open ↑U → IsClosed ↑…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Valued.instIsTopologicalRing`：∀ {R : Type u} [inst : Ring R] {Γ₀ : Type 
v} [inst_1 : LinearOrderedCommGroupWithZero Γ₀] [_i : Valued R Γ₀],   IsTopologi
calRing R
· 使用定理 `Valued.isOpen_ball`：isOpen_ball (r : ValueGroup₀ (.ofClass _i.v)) : IsOp
en {x | v.restrict x < r}

--- 原说明 ---
An open ball centred at the origin in a valued ring is closed.
-/
theorem isClosed_ball (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClosed {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _ _)

/-- An open ball centred at the origin in a valued ring is clopen. -/
/-
**Valued.isClopen_ball** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClopen_ball (r : ValueGroup₀ (.ofClass _i.v)) : IsClopen {x | v.restrict
 x < r}
参数：r : ValueGroup₀ (.ofClass _i.v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.isClosed_ball`：isClosed_ball (r : ValueGroup₀ (.ofClass _i.v)) : 
IsClosed {x | v.restrict x < r}
· 使用定理 `Valued.isOpen_ball`：isOpen_ball (r : ValueGroup₀ (.ofClass _i.v)) : IsOp
en {x | v.restrict x < r}

--- 原说明 ---
An open ball centred at the origin in a valued ring is clopen.
-/
theorem isClopen_ball (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClopen {x | v.restrict x < r} :=
  ⟨isClosed_ball _ _, isOpen_ball _ _⟩

/-- A closed ball centred at the origin in a valued ring is open. -/
/-
**Valued.isOpen_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isOpen_closedBall {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) : IsOpen
 {x | v.restrict x <= r}
参数：.ofClass _i.v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Valued.mem_nhds`：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (M
onoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.
1 } s…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
A closed ball centred at the origin in a valued ring is open.
-/
theorem isOpen_closedBall {r : ValueGroup₀ (.ofClass _i.v)} (hr : r ≠ 0) :
  IsOpen {x | v.restrict x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy ↦
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A closed ball centred at the origin in a valued ring is closed. -/
/-
**Valued.isClosed_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClosed_closedBall (r : ValueGroup₀ (.ofClass _i.v)) : IsClosed {x | v.re
strict x <= r}
参数：r : ValueGroup₀ (.ofClass _i.v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Valued.mem_nhds`：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (M
onoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.
1 } s…
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Valuation.map_sub_eq_of_lt_left`：map_sub_eq_of_lt_left (h : v y < v x) :
 v (x - y) = v x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Valuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x)

--- 原说明 ---
A closed ball centred at the origin in a valued ring is closed.
-/
theorem isClosed_closedBall (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClosed {x | v.restrict x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v.restrict x ≠ 0 := hx.ne_zero
  exact ⟨Units.mk0 _ hx', fun y hy hy' ↦ ne_of_lt hy <| map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

/-- A closed ball centred at the origin in a valued ring is clopen. -/
/-
**Valued.isClopen_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClopen_closedBall {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) : IsCl
open {x | v.restrict x <= r}
参数：.ofClass _i.v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.isClosed_closedBall`：isClosed_closedBall (r : ValueGroup₀ (.ofCla
ss _i.v)) : IsClosed {x | v.restrict x <= r}
· 使用定理 `Valued.isOpen_closedBall`：isOpen_closedBall {r : ValueGroup₀ (.ofClass _
i.v)} (hr : r != 0) : IsOpen {x | v.restrict x <= r}

--- 原说明 ---
A closed ball centred at the origin in a valued ring is clopen.
-/
theorem isClopen_closedBall {r : ValueGroup₀ (.ofClass _i.v)} (hr : r ≠ 0) :
    IsClopen {x | v.restrict x ≤ r} :=
  ⟨isClosed_closedBall _ _, isOpen_closedBall _ hr⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A sphere centred at the origin in a valued ring is clopen. -/
/-
**Valued.isClopen_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClopen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) : IsClopen
 {x | v.restrict x = r}
参数：.ofClass _i.v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClopen.diff`：IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClo
pen (s \ t)
· 使用定理 `Valued.isClopen_closedBall`：isClopen_closedBall {r : ValueGroup₀ (.ofCla
ss _i.v)} (hr : r != 0) : IsClopen {x | v.restrict x <= r}
· 使用定理 `Valued.isClopen_ball`：isClopen_ball (r : ValueGroup₀ (.ofClass _i.v)) : 
IsClopen {x | v.restrict x < r}

--- 原说明 ---
A sphere centred at the origin in a valued ring is clopen.
-/
theorem isClopen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (hr : r ≠ 0) :
    IsClopen {x | v.restrict x = r} := by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x ≤ r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall _ hr) (isClopen_ball _ _)

/-- A sphere centred at the origin in a valued ring is open. -/
/-
**Valued.isOpen_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isOpen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) : IsOpen {x 
| v.restrict x = r}
参数：.ofClass _i.v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Valued.isClopen_sphere`：isClopen_sphere {r : ValueGroup₀ (.ofClass _i.v)
} (hr : r != 0) : IsClopen {x | v.restrict x = r}

--- 原说明 ---
A sphere centred at the origin in a valued ring is open.
-/
theorem isOpen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (hr : r ≠ 0) :
    IsOpen {x | v.restrict x = r} :=
  isClopen_sphere _ hr |>.isOpen

/-- A sphere centred at the origin in a valued ring is closed. -/
/-
**Valued.isClosed_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClosed_sphere (r : ValueGroup₀ (.ofClass _i.v)) : IsClosed {x | v.restri
ct x = r}
参数：r : ValueGroup₀ (.ofClass _i.v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Valued.isClosed_closedBall`：isClosed_closedBall (r : ValueGroup₀ (.ofCla
ss _i.v)) : IsClosed {x | v.restrict x <= r}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `Valued.isClopen_sphere`：isClopen_sphere {r : ValueGroup₀ (.ofClass _i.v)
} (hr : r != 0) : IsClopen {x | v.restrict x = r}

--- 原说明 ---
A sphere centred at the origin in a valued ring is closed.
-/
theorem isClosed_sphere (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClosed {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa using isClosed_closedBall R 0
  exact isClopen_sphere _ hr |>.isClosed

/-- The closed unit ball in a valued ring is open. -/
/-
**Valued.isOpen_integer** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isOpen_integer : IsOpen (_i.v.integer : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_le_one_iff`：restrict_le_one_iff {x : R} : v.restrict 
x <= 1 ↔ v x <= 1
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Subsemiring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocSemiring R] (t
oSubmonoid toSubmonoid_1 : Submonoid R)   (e_toSubmonoid : toSubmonoid = toSubmo
noid_1)   (add_…
· 使用定理 `Subring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocRing R] (toSubsemi
ring toSubsemiring_1 : Subsemiring R)   (e_toSubsemiring : toSubsemiring = toSub
semiring_1)…
· 使用定理 `Valued.isOpen_closedBall`：isOpen_closedBall {r : ValueGroup₀ (.ofClass _
i.v)} (hr : r != 0) : IsOpen {x | v.restrict x <= r}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P

--- 原说明 ---
The closed unit ball in a valued ring is open.
-/
theorem isOpen_integer : IsOpen (_i.v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isOpen_closedBall _ one_ne_zero

/-- The closed unit ball of a valued ring is closed. -/
/-
**Valued.isClosed_integer** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClosed_integer : IsClosed (_i.v.integer : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_le_one_iff`：restrict_le_one_iff {x : R} : v.restrict 
x <= 1 ↔ v x <= 1
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Subsemiring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocSemiring R] (t
oSubmonoid toSubmonoid_1 : Submonoid R)   (e_toSubmonoid : toSubmonoid = toSubmo
noid_1)   (add_…
· 使用定理 `Subring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocRing R] (toSubsemi
ring toSubsemiring_1 : Subsemiring R)   (e_toSubsemiring : toSubsemiring = toSub
semiring_1)…
· 使用定理 `Valued.isClosed_closedBall`：isClosed_closedBall (r : ValueGroup₀ (.ofCla
ss _i.v)) : IsClosed {x | v.restrict x <= r}

--- 原说明 ---
The closed unit ball of a valued ring is closed.
-/
theorem isClosed_integer : IsClosed (_i.v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _ _

/-- The closed unit ball of a valued ring is clopen. -/
/-
**Valued.isClopen_integer** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClopen_integer : IsClopen (_i.v.integer : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valued.isClosed_integer`：isClosed_integer : IsClosed (_i.v.integer : Set
 R)
· 使用定理 `Valued.isOpen_integer`：isOpen_integer : IsOpen (_i.v.integer : Set R)

--- 原说明 ---
The closed unit ball of a valued ring is clopen.
-/
theorem isClopen_integer : IsClopen (_i.v.integer : Set R) :=
  ⟨isClosed_integer _, isOpen_integer _⟩

/-- The valuation subring of a valued field is open. -/
/-
**Valued.isOpen_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isOpen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] : IsOpen
 (hv.v.valuationSubring : Set K)
参数：K : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valued.isOpen_integer`：isOpen_integer : IsOpen (_i.v.integer : Set R)

--- 原说明 ---
The valuation subring of a valued field is open.
-/
theorem isOpen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  isOpen_integer K

/-- The valuation subring of a valued field is closed. -/
/-
**Valued.isClosed_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClosed_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] : IsCl
osed (hv.v.valuationSubring : Set K)
参数：K : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valued.isClosed_integer`：isClosed_integer : IsClosed (_i.v.integer : Set
 R)

--- 原说明 ---
The valuation subring of a valued field is closed.
-/
theorem isClosed_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClosed (hv.v.valuationSubring : Set K) :=
  isClosed_integer K

/-- The valuation subring of a valued field is clopen. -/
/-
**Valued.isClopen_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：isClopen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] : IsCl
open (hv.v.valuationSubring : Set K)
参数：K : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valued.isClopen_integer`：isClopen_integer : IsClopen (_i.v.integer : Set
 R)

--- 原说明 ---
The valuation subring of a valued field is clopen.
-/
theorem isClopen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClopen (hv.v.valuationSubring : Set K) :=
  isClopen_integer K

end Valued


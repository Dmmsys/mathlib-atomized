/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Covering maps involving `AddCircle`

-/

public section

namespace AddCircle

section AddCommGroup

open AddSubgroup

variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  [DiscreteTopology (zmultiples p)]

/-
**AddCircle.isAddQuotientCoveringMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：isAddQuotientCoveringMap_coe : IsAddQuotientCoveringMap ((↑) : 𝕜 -> AddCir
cle p) (zmultiples p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.isAddQuotientCoveringMap_of_comm`：∀ {G : Type u_4} [inst : A
ddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] (S : AddS
ubgroup G),   IsDiscrete ↑S → IsAd…
· 使用引理 `DiscreteTopology.isDiscrete`：DiscreteTopology.isDiscrete [DiscreteTopolo
gy s] : IsDiscrete s
-/
theorem isAddQuotientCoveringMap_coe :
    IsAddQuotientCoveringMap ((↑) : 𝕜 → AddCircle p) (zmultiples p) :=
  isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete
/-
**AddCircle.isCoveringMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 -> AddCircle p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddQuotientCoveringMap.isCoveringMap`：∀ {E : Type u_1} {X : Type u_2} 
[inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] (f : E → X) (G : Type 
u_3)   [inst_2 : AddGroup G]…
· 使用定理 `AddCircle.isAddQuotientCoveringMap_coe`：isAddQuotientCoveringMap_coe : I
sAddQuotientCoveringMap ((↑) : 𝕜 -> AddCircle p) (zmultiples p)
-/
theorem isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p) :=
  (isAddQuotientCoveringMap_coe p).isCoveringMap
/-
**AddCircle.isLocalHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：isLocalHomeomorph_coe : IsLocalHomeomorph ((↑) : 𝕜 -> AddCircle p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
· 使用定理 `AddCircle.isCoveringMap_coe`：isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 
-> AddCircle p)
-/
theorem isLocalHomeomorph_coe : IsLocalHomeomorph ((↑) : 𝕜 → AddCircle p) :=
  (isCoveringMap_coe p).isLocalHomeomorph

end AddCommGroup

section Field

open Topology

variable {𝕜 : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [IsTopologicalRing 𝕜]
variable (p : 𝕜) [T0Space (AddCircle p)]

-- TODO: this comment seems outdated?
/- This instance can be supplied from:
- `[NormedSpace ℚ 𝕜]` (with import `Mathlib.Analysis.Normed.Module.Basic`), or
- `[LinearOrder 𝕜] [IsOrderedMonoid 𝕜] [OrderTopology 𝕜]`
  (with import `Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete`)
and `𝕜 := ℝ` satisfies both. -/

/-
**AddCircle.isAddQuotientCoveringMap_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`
。
形式化陈述：isAddQuotientCoveringMap_zsmul {n : Int} (hn : IsUnit (n : 𝕜)) : IsAddQuot
ientCoveringMap (n • · : AddCircle p -> _) (zsmulAddGroupHom (α
参数：hn : IsUnit (n : 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isAddQuotientCoveringMap_of_isDiscrete_ker_addMon
oidHom`：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : To
pologicalSpace X] [inst_2 : AddGroup E]   [IsTopologicalAddGroup E] …
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.instIsTopologicalAddGroup`：∀ {G : Type u_1} [inst : Top
ologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (N : AddSubgrou
p G)   [inst_3 : N.Normal], IsTo…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsUnit.isQuotientMap_zsmul`：isQuotientMap_zsmul {M β} [Ring M] [AddCommG
roup α] [Module M α] [ContinuousConstSMul M α] [AddGroup β] (f : α ->+ β) [Topol
ogicalSpace β] (…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
· 使用引理 `Set.Finite.isDiscrete`：Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs
 : s.Finite) : IsDiscrete s
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `AddCircle.finite_torsion_of_isSMulRegular_int`：finite_torsion_of_isSMulR
egular_int (n : Int) (hn : IsSMulRegular 𝕜 n) : {x : AddCircle p | n • x = 0}.Fi
nite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `IsUnit.isSMulRegular`：IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegul
ar M a

--- 原说明 ---
This instance can be supplied from:
- `[NormedSpace ℚ 𝕜]` (with import `Mathlib.Analysis.Normed.Module.Basic`), or
- `[LinearOrder 𝕜] [IsOrderedMonoid 𝕜] [OrderTopology 𝕜]`
  (with import `Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete`)
and `𝕜 := ℝ` satisfies both.
-/
theorem isAddQuotientCoveringMap_zsmul {n : ℤ} (hn : IsUnit (n : 𝕜)) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (zsmulAddGroupHom (α := AddCircle p) n).ker := by
  refine hn.isQuotientMap_zsmul (QuotientAddGroup.mk' _) isQuotientMap_quotient_mk'
    |>.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (f := zsmulAddGroupHom (α := AddCircle p) n)
    (Set.Finite.isDiscrete <| finite_torsion_of_isSMulRegular_int _ _ fun _ ↦ ?_)
  simp_rw [zsmul_eq_mul]
  apply hn.isSMulRegular 𝕜
/-
**AddCircle.isAddQuotientCoveringMap_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`
。
形式化陈述：isAddQuotientCoveringMap_nsmul {n : Nat} (hn : IsUnit (n : 𝕜)) : IsAddQuot
ientCoveringMap (n • · : AddCircle p -> _) (nsmulAddMonoidHom (α
参数：hn : IsUnit (n : 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `QuotientAddGroup.addMonoidHom_ext`：∀ {G : Type u_1} {M : Type u_4} [inst
 : AddGroup G] [inst_1 : AddMonoid M] (N : AddSubgroup G) [nN : N.Normal]   ⦃f g
 : G ⧸ N →+ M⦄, f.comp …
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmulAddMonoidHom_apply`：∀ {α : Type u_1} [inst : AddCommMonoid α] (n : 
ℕ) (x : α), (nsmulAddMonoidHom n) x = n • x
· 使用定理 `zsmulAddGroupHom_apply`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α
] (n : ℤ) (x : α), (zsmulAddGroupHom n) x = n • x
· 使用定理 `AddCircle.isAddQuotientCoveringMap_zsmul`：isAddQuotientCoveringMap_zsmul
 {n : Int} (hn : IsUnit (n : 𝕜)) : IsAddQuotientCoveringMap (n • · : AddCircle p
 -> _) (zsmulAddGroupHom (α
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
theorem isAddQuotientCoveringMap_nsmul {n : ℕ} (hn : IsUnit (n : 𝕜)) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (nsmulAddMonoidHom (α := AddCircle p) n).ker := by
  convert! isAddQuotientCoveringMap_zsmul p (n := n) (mod_cast hn)
  all_goals ext; simp
/-
**AddCircle.isAddQuotientCoveringMap_zsmul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`AddCircle`。
形式化陈述：isAddQuotientCoveringMap_zsmul_of_ne_zero [Algebra Rat 𝕜] (n : Int) [NeZer
o n] : IsAddQuotientCoveringMap (n • · : AddCircle p -> _) (zsmulAddGroupHom (α
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.isAddQuotientCoveringMap_zsmul`：isAddQuotientCoveringMap_zsmul
 {n : Int} (hn : IsUnit (n : 𝕜)) : IsAddQuotientCoveringMap (n • · : AddCircle p
 -> _) (zsmulAddGroupHom (α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem isAddQuotientCoveringMap_zsmul_of_ne_zero [Algebra ℚ 𝕜] (n : ℤ) [NeZero n] :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (zsmulAddGroupHom (α := AddCircle p) n).ker :=
  isAddQuotientCoveringMap_zsmul p (n := n) <| by
    convert! (Int.cast_ne_zero.mpr <| NeZero.ne n).isUnit.map (algebraMap ℚ 𝕜); simp
/-
**AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`AddCircle`。
形式化陈述：isAddQuotientCoveringMap_nsmul_of_ne_zero [Algebra Rat 𝕜] (n : Nat) [NeZer
o n] : IsAddQuotientCoveringMap (n • · : AddCircle p -> _) (nsmulAddMonoidHom (α
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.isAddQuotientCoveringMap_nsmul`：isAddQuotientCoveringMap_nsmul
 {n : Nat} (hn : IsUnit (n : 𝕜)) : IsAddQuotientCoveringMap (n • · : AddCircle p
 -> _) (nsmulAddMonoidHom (α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem isAddQuotientCoveringMap_nsmul_of_ne_zero [Algebra ℚ 𝕜] (n : ℕ) [NeZero n] :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (nsmulAddMonoidHom (α := AddCircle p) n).ker :=
  isAddQuotientCoveringMap_nsmul p (n := n) <| by
    convert! (Nat.cast_ne_zero.mpr <| NeZero.ne n).isUnit.map (algebraMap ℚ 𝕜); simp

end Field

end AddCircle


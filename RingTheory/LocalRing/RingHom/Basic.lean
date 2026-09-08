/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!

# Local rings homomorphisms

We prove basic properties of local rings homomorphisms.

-/

public section

variable {R S T : Type*}
section

variable [Semiring R] [Semiring S] [Semiring T]

@[instance]
/-
**isLocalHom_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_id (R : Type*) [Semiring R] : IsLocalHom (RingHom.id R) where m
ap_nonunit _
参数：R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalHom_id (R : Type*) [Semiring R] : IsLocalHom (RingHom.id R) where
  map_nonunit _ := id

-- see note [lower instance priority]
@[instance 100]
/-
**isLocalHom_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_toRingHom {F : Type*} [FunLike F R S] [RingHomClass F R S] (f :
 F) [IsLocalHom f] : IsLocalHom (f : R ->+* S)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
theorem isLocalHom_toRingHom {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R →+* S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

@[instance]
/-
**RingHom.isLocalHom_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isLocalHom_comp (g : S ->+* T) (f : R ->+* S) [IsLocalHom g] [IsLo
calHom f] : IsLocalHom (g.comp f) where map_nonunit a
参数：g : S ->+* T；f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
theorem RingHom.isLocalHom_comp (g : S →+* T) (f : R →+* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)
/-
**isLocalHom_of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_of_comp (f : R ->+* S) (g : S ->+* T) [IsLocalHom (g.comp f)] :
 IsLocalHom f
参数：f : R ->+* S；g : S ->+* T；g.comp f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
-/
theorem isLocalHom_of_comp (f : R →+* S) (g : S →+* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

/-- If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is. -/
/-
**RingHom.domain_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.domain_isLocalRing [IsLocalRing S] (f : R ->+* S) [IsLocalHom f] :
 IsLocalRing R where toNontrivial
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_add_one`：∀ {R : Type u_1} {inst : Semiri
ng R} [self : IsLocalRing R] {a b : R}, a + b = 1 → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If `f : R →+* S` is a local ring hom, then `R` is a local ring if `S` is.
-/
theorem RingHom.domain_isLocalRing [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    IsLocalRing R where
  toNontrivial := f.domain_nontrivial
  isUnit_or_isUnit_of_add_one {a b} h := Or.imp
    (isUnit_of_map_unit f a) (isUnit_of_map_unit f b)
    (IsLocalRing.isUnit_or_isUnit_of_add_one (by rw [← map_add, h, map_one]))

end

section

open IsLocalRing

variable [CommSemiring R] [IsLocalRing R] [CommSemiring S] [IsLocalRing S]

/--
The image of the maximal ideal of the source is contained within the maximal ideal of the target.
-/
/-
**map_nonunit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nonunit (f : R ->+* S) [IsLocalHom f] (a : R) (h : a in maximalIdeal R
) : f a in maximalIdeal S
参数：f : R ->+* S；a : R；h : a in maximalIdeal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …

--- 原说明 ---
The image of the maximal ideal of the source is contained within the maximal ide
al of the target.
-/
theorem map_nonunit (f : R →+* S) [IsLocalHom f] (a : R) (h : a ∈ maximalIdeal R) :
    f a ∈ maximalIdeal S := fun H => h <| isUnit_of_map_unit f a H

end

namespace IsLocalRing

section

variable [CommSemiring R] [IsLocalRing R] [CommSemiring S] [IsLocalRing S]

/-- A ring homomorphism between local rings is a local ring hom iff it reflects units,
i.e. any preimage of a unit is still a unit. -/
@[stacks 07BJ]
/-
**IsLocalRing.local_hom_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：local_hom_TFAE (f : R ->+* S) : List.TFAE [IsLocalHom f, f '' maximalIdeal
 R subseteq maximalIdeal S, (maximalIdeal R).map f <= maximalIdeal S, maximalIde
al R <= (maximalIdeal S).comap f, (maximalIdeal S).comap f = maximalIdeal R]
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nonunit`：map_nonunit (f : R ->+* S) [IsLocalHom f] (a : R) (h : a in
 maximalIdeal R) : f a in maximalIdeal S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
A ring homomorphism between local rings is a local ring hom iff it reflects unit
s,
i.e. any preimage of a unit is still a unit.
-/
theorem local_hom_TFAE (f : R →+* S) :
    List.TFAE
      [IsLocalHom f, f '' maximalIdeal R ⊆ maximalIdeal S,
        (maximalIdeal R).map f ≤ maximalIdeal S, maximalIdeal R ≤ (maximalIdeal S).comap f,
        (maximalIdeal S).comap f = maximalIdeal R] := by
  tfae_have 1 → 2
  | _, _, ⟨a, ha, rfl⟩ => map_nonunit f a ha
  tfae_have 2 → 4 := Set.image_subset_iff.1
  tfae_have 3 ↔ 4 := Ideal.map_le_iff_le_comap
  tfae_have 4 → 1 := fun h ↦ ⟨fun x => not_imp_not.1 (@h x)⟩
  tfae_have 1 → 5
  | _ => by ext; exact not_iff_not.2 (isUnit_map_iff f _)
  tfae_have 5 → 4 := fun h ↦ le_of_eq h.symm
  tfae_finish
/-
**IsLocalRing.maximalIdeal_comap** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：maximalIdeal_comap (f : R ->+* S) [IsLocalHom f] : (maximalIdeal S).comap 
f = maximalIdeal R
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
-/
lemma maximalIdeal_comap (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R :=
  ((local_hom_TFAE _).out 0 4).mp ‹_›
/-
**IsLocalRing.map_maximalIdeal_le** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：map_maximalIdeal_le (f : R ->+* S) [IsLocalHom f] : (maximalIdeal R).map f
 <= maximalIdeal S
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `IsLocalRing.maximalIdeal_comap`：maximalIdeal_comap (f : R ->+* S) [IsLoc
alHom f] : (maximalIdeal S).comap f = maximalIdeal R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_maximalIdeal_le (f : R →+* S) [IsLocalHom f] :
    (maximalIdeal R).map f ≤ maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
/-
**IsLocalRing.map_maximalIdeal_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：map_maximalIdeal_lt_top (f : R ->+* S) [IsLocalHom f] : (maximalIdeal R).m
ap f < ⊤
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `IsLocalRing.map_maximalIdeal_le`：map_maximalIdeal_le (f : R ->+* S) [IsL
ocalHom f] : (maximalIdeal R).map f <= maximalIdeal S
· 使用定理 `Ideal.IsMaximal.lt_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I < ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem map_maximalIdeal_lt_top (f : R →+* S) [IsLocalHom f] : (maximalIdeal R).map f < ⊤ :=
  (map_maximalIdeal_le f).trans_lt (maximalIdeal.isMaximal S).lt_top

end

/-
**IsLocalRing.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_surjective [CommSemiring R] [IsLocalRing R] [Semiring S] [Nontrivial S]
 (f : R ->+* S) [IsLocalHom f] (hf : Function.Surjective f) : IsLocalRing S
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add`：of_isUnit_or_isUnit_of_is
Unit_add [Nontrivial R] (h : forall a b : R, IsUnit (a + b) -> IsUnit a ∨ IsUnit
 b) : IsLocalRing R
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`：isUnit_or_isUnit_of_isUnit_a
dd {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem of_surjective [CommSemiring R] [IsLocalRing R] [Semiring S] [Nontrivial S] (f : R →+* S)
    [IsLocalHom f] (hf : Function.Surjective f) : IsLocalRing S :=
  of_isUnit_or_isUnit_of_isUnit_add (by
    intro a b hab
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    rw [← map_add] at hab
    exact
      (isUnit_or_isUnit_of_isUnit_add <| IsLocalHom.map_nonunit _ hab).imp f.isUnit_map
        f.isUnit_map)
/-
**IsLocalRing._root_.IsLocalHom.of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `IsLocal
Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsLocalHom.of_surjective [CommRing R] [CommRing S] [Nontrivial S] [IsLocalRing R]
    (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalHom f := by
  have := IsLocalRing.of_surjective' f ‹_›
  refine ((local_hom_TFAE f).out 3 0).mp ?_
  have := Ideal.comap_isMaximal_of_surjective f hf (K := maximalIdeal S)
  exact ((maximal_ideal_unique R).unique (inferInstanceAs (maximalIdeal R).IsMaximal) this).le

alias _root_.Function.Surjective.isLocalHom := _root_.IsLocalHom.of_surjective

/-- If `f : R →+* S` is a surjective local ring hom, then the induced units map is surjective. -/
/-
**IsLocalRing.surjective_units_map_of_local_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `I
sLocalRing`。
形式化陈述：surjective_units_map_of_local_ringHom [Semiring R] [Semiring S] (f : R ->+
* S) (hf : Function.Surjective f) (h : IsLocalHom f) : Function.Surjective (Unit
s.map <| f.toMonoidHom)
参数：f : R ->+* S；hf : Function.Surjective f；h : IsLocalHom f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v

--- 原说明 ---
If `f : R →+* S` is a surjective local ring hom, then the induced units map is s
urjective.
-/
theorem surjective_units_map_of_local_ringHom [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Surjective f) (h : IsLocalHom f) :
    Function.Surjective (Units.map <| f.toMonoidHom) := by
  intro a
  obtain ⟨b, hb⟩ := hf (a : S)
  use (isUnit_of_map_unit f b (by rw [hb]; exact Units.isUnit _)).unit
  ext
  exact hb

-- see Note [lower instance priority]
/-- Every ring hom `f : K →+* R` from a division ring `K` to a nontrivial ring `R` is a
local ring hom. -/
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every ring hom `f : K →+* R` from a division ring `K` to a nontrivial ring `R` i
s a
local ring hom.
-/
instance (priority := 100) {K R} [DivisionRing K] [CommRing R] [Nontrivial R]
    (f : K →+* R) : IsLocalHom f where
  map_nonunit r hr := by simpa only [isUnit_iff_ne_zero, ne_eq, map_eq_zero] using hr.ne_zero
/-
**IsLocalRing.map_maximalIdeal_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalR
ing`。
形式化陈述：map_maximalIdeal_of_surjective [CommRing R] [CommRing S] [IsLocalRing R] [
IsLocalRing S] (f : R ->+* S) (hf : Function.Surjective f) : (maximalIdeal R).ma
p f = maximalIdeal S
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.of_surjective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] [Nontrivial S] [IsLocalRing R] (f : R →+* S),   Func
tion.Surjectiv…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalRing.maximalIdeal_comap`：maximalIdeal_comap (f : R ->+* S) [IsLoc
alHom f] : (maximalIdeal S).comap f = maximalIdeal R
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
-/
lemma map_maximalIdeal_of_surjective [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) : (maximalIdeal R).map f = maximalIdeal S := by
  let := IsLocalHom.of_surjective f hf
  rw [← maximalIdeal_comap f, Ideal.map_comap_of_surjective f hf]

@[simp]
/-
**IsLocalRing.map_ringEquiv_maximalIdeal** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`
。
形式化陈述：map_ringEquiv_maximalIdeal [CommRing R] [CommRing S] [IsLocalRing R] [IsLo
calRing S] (e : R ≃+* S) : (maximalIdeal R).map e = maximalIdeal S
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.map_maximalIdeal_of_surjective`：map_maximalIdeal_of_surjecti
ve [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (f : R ->+* S) (hf 
: Function.Surjective f) : (maxi…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
lemma map_ringEquiv_maximalIdeal [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : (maximalIdeal R).map e = maximalIdeal S :=
  map_maximalIdeal_of_surjective (e : R →+* S) e.surjective

end IsLocalRing

namespace RingEquiv

/-
**RingEquiv.isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {A : Type u_4} {B : Type u_5} [inst : CommSemiring A] [IsLocalRing A] [i
nst_2 : Semiring B] (e : A ≃+* B),   IsLocalRing B
参数：e : A ≃+* B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_surjective`：of_surjective [CommSemiring R] [IsLocalRing R
] [Semiring S] [Nontrivial S] (f : R ->+* S) [IsLocalHom f] (hf : Function.Surje
ctive f) : IsLo…
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `isLocalHom_toRingHom`：isLocalHom_toRingHom {F : Type*} [FunLike F R S] [
RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R ->+* S)
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
protected theorem isLocalRing {A B : Type*} [CommSemiring A] [IsLocalRing A] [Semiring B]
    (e : A ≃+* B) : IsLocalRing B :=
  haveI := e.symm.toEquiv.nontrivial
  IsLocalRing.of_surjective (e : A →+* B) e.surjective

end RingEquiv

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} [Nontrivial (ZMod n)] (f : R →+* ZMod n) :
    IsLocalHom f :=
  (ZMod.ringHom_surjective f).isLocalHom

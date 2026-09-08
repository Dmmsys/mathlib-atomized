/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Monomorphisms and epimorphisms in `Group`

In this file, we prove monomorphisms in the category of groups are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/

@[expose] public section


noncomputable section

open scoped Pointwise

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

@[to_additive]
/-
**MonoidHom.ker_eq_bot_of_cancel** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_eq_bot_of_cancel {f : A ->* B} (h : forall u v : f.ker ->* A, f.comp u
 = f.comp v -> u = v) : f.ker = ⊥
参数：h : forall u v : f.ker ->* A, f.comp u = f.comp v -> u = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `MonoidHom.range_one`：range_one : (1 : G ->* N).range = ⊥
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MonoidHom.comp_one`：comp_one [MulOne M] [MulOneClass N] [MulOneClass P] 
(f : N ->* P) : f.comp (1 : M ->* N) = 1
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using congr_arg range (h f.ker.subtype 1 (by cat_disch))

end

section

variable [CommGroup A] [CommGroup B]

@[to_additive]
/-
**MonoidHom.range_eq_top_of_cancel** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：range_eq_top_of_cancel {f : A ->* B} (h : forall u v : B ->* B ⧸ f.range, 
u.comp f = v.comp f -> u = v) : f.range = ⊤
参数：h : forall u v : B ->* B ⧸ f.range, u.comp f = v.comp f -> u = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `QuotientGroup.mk_one`：mk_one : ((1 : G) : Q) = 1
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `MonoidHom.ker_one`：ker_one : (1 : G ->* M).ker = ⊤
-/
theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ := by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.range).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h

end

end MonoidHom

section

open CategoryTheory

namespace GrpCat

variable {A B : GrpCat.{u}} (f : A ⟶ B)

@[to_additive]
/-
**GrpCat.ker_eq_bot_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ker_eq_bot_of_cancel`：ker_eq_bot_of_cancel {f : A ->* B} (h : 
forall u v : f.ker ->* A, f.comp u = f.comp v -> u = v) : f.ker = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.ext_iff`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : 
(X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
-/
theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 <| ConcreteCategory.ext h

@[to_additive]
/-
**GrpCat.mono_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GrpCat.ker_eq_bot_of_mono`：ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
-/
theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]
/-
**GrpCat.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：mono_iff_injective : Mono f ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `GrpCat.mono_iff_ker_eq_bot`：mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f.hom

namespace SurjectiveOfEpiAuxs

local notation3 "X" => Set.range (· • (f.hom.range : Set B) : B → Set B)

/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
/-
**GrpCat.SurjectiveOfEpiAuxs.XWithInfinity** 是 Mathlib 中的一个归纳类型，位于命名空间 `GrpCat.S
urjectiveOfEpiAuxs`。
形式化陈述：{A B : GrpCat} → (A ⟶ B) → Type u
参数：A ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
inductive XWithInfinity
  | fromCoset : X → XWithInfinity
  | infinity : XWithInfinity

open XWithInfinity Equiv.Perm

local notation "X'" => XWithInfinity f

local notation "∞" => XWithInfinity.infinity

local notation "SX'" => Equiv.Perm X'
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul B X' where
  smul b x :=
    match x with
    | fromCoset y => fromCoset ⟨b • y, by
          rw [← y.2.choose_spec, leftCoset_assoc]
          let b' : B := y.2.choose
          use b * b'⟩
    | ∞ => ∞
/-
**GrpCat.SurjectiveOfEpiAuxs.mul_smul** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Surjecti
veOfEpiAuxs`。
形式化陈述：mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x
参数：b b' : B；x : X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `leftCoset_assoc`：leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (
a * b) • s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl
/-
**GrpCat.SurjectiveOfEpiAuxs.one_smul** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Surjecti
veOfEpiAuxs`。
形式化陈述：one_smul (x : X') : (1 : B) • x = x
参数：x : X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_smul (x : X') : (1 : B) • x = x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset]
  | ∞ => rfl
/-
**GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range** 是 Mathlib 中的一个定理，位于命名空间
 `GrpCat.SurjectiveOfEpiAuxs`。
形式化陈述：fromCoset_eq_of_mem_range {b : B} (hb : b in f.hom.range) : fromCoset ⟨b •
 ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
参数：hb : b in f.hom.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `leftCoset_eq_iff`：leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔
 x⁻¹ * y in s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
theorem fromCoset_eq_of_mem_range {b : B} (hb : b ∈ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  congr
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个示例，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (G : Type) [Group G] (S : Subgroup G) : Set G := S

set_option backward.isDefEq.respectTransparency.types false in
/-
**GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range** 是 Mathlib 中的一个定理，位于命名空间
 `GrpCat.SurjectiveOfEpiAuxs`。
形式化陈述：fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.hom.range) : fromCoset ⟨b • 
↑f.hom.range, b, rfl⟩ != fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
参数：hb : b ∉ f.hom.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `leftCoset_eq_iff`：leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔
 x⁻¹ * y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.XWithInfinity.fromCoset.injEq`：∀ {A B : GrpCa
t} {f : A ⟶ B} (a a_1 : ↑(Set.range fun x => x • ↑(GrpCat.Hom.hom f).range)),   
(GrpCat.SurjectiveOfEpiAuxs.XWithInfinity.from…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ ≠ fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq X' :=
  Classical.decEq _

/-- Let `τ` be the permutation on `X'` exchanging `f.hom.range` and the point at infinity.
-/
/-
**GrpCat.SurjectiveOfEpiAuxs.tau** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.SurjectiveOfE
piAuxs`。
形式化陈述：tau : SX'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `τ` be the permutation on `X'` exchanging `f.hom.range` and the point at inf
inity.
-/
noncomputable def tau : SX' :=
  Equiv.swap (fromCoset ⟨↑f.hom.range, ⟨1, one_leftCoset _⟩⟩) ∞

local notation "τ" => tau f
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem τ_apply_infinity : τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ :=
  Equiv.swap_apply_right _ _
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem τ_apply_fromCoset : τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ :=
  Equiv.swap_apply_left _ _
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem τ_apply_fromCoset' (x : B) (hx : x ∈ f.hom.range) :
    τ (fromCoset ⟨x • ↑f.hom.range, ⟨x, rfl⟩⟩) = ∞ :=
  (fromCoset_eq_of_mem_range _ hx).symm ▸ τ_apply_fromCoset _
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem τ_symm_apply_fromCoset :
    Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_left]
/-
**GrpCat.SurjectiveOfEpiAuxs.** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.SurjectiveOfEpiA
uxs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem τ_symm_apply_infinity :
    Equiv.symm τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_right]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β • y`.
-/
/-
**GrpCat.SurjectiveOfEpiAuxs.g** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.SurjectiveOfEpi
Auxs`。
形式化陈述：g : B ->* SX' where toFun β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the func
tion sending
point at infinity to point at infinity and sending coset `y` to `β • y`.
-/
def g : B →* SX' where
  toFun β :=
    { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul, mul_inv_cancel, one_smul] }
  map_one' := by
    ext
    simp [one_smul]
  map_mul' b1 b2 := by
    ext
    simp [mul_smul]

local notation "g" => g f

/-- Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
/-
**GrpCat.SurjectiveOfEpiAuxs.h** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.SurjectiveOfEpi
Auxs`。
形式化陈述：h : B ->* SX' where toFun β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def h : B →* SX' where
  toFun β := ((τ).symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp

local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.hom.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.hom.range`, then `h x ≠ g x` at the coset
  `f.hom.range`.
-/


/-
**GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat
.SurjectiveOfEpiAuxs`。
形式化陈述：g_apply_fromCoset (x : B) (y : X) : g x (fromCoset y) = fromCoset ⟨x • ↑y,
 by obtain ⟨z, hz⟩
参数：x : B；y : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strategy is the following: assuming `epi f`
* prove that `f.hom.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.hom.range`, then `h x ≠ g x` at
 the coset
  `f.hom.range`.
-/
theorem g_apply_fromCoset (x : B) (y : X) :
    g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl
/-
**GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.
SurjectiveOfEpiAuxs`。
形式化陈述：g_apply_infinity (x : B) : (g x) ∞ = ∞
参数：x : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ := rfl
/-
**GrpCat.SurjectiveOfEpiAuxs.h_apply_infinity** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.
SurjectiveOfEpiAuxs`。
形式化陈述：h_apply_infinity (x : B) (hx : x in f.hom.range) : (h x) ∞ = ∞
参数：x : B；hx : x in f.hom.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity`：τ_symm_apply_infinity 
: Equiv.symm τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset`：g_apply_fromCoset (x : B) 
(y : X) : g x (fromCoset y) = fromCoset ⟨x • ↑y, by obtain ⟨z, hz⟩
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset'`：τ_apply_fromCoset' (x : B
) (hx : x in f.hom.range) : τ (fromCoset ⟨x • ↑f.hom.range, ⟨x, rfl⟩⟩) = ∞
-/
theorem h_apply_infinity (x : B) (hx : x ∈ f.hom.range) : (h x) ∞ = ∞ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity, g_apply_fromCoset]
  exact τ_apply_fromCoset' f x hx
/-
**GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat
.SurjectiveOfEpiAuxs`。
形式化陈述：h_apply_fromCoset (x : B) : (h x) (fromCoset ⟨f.hom.range, 1, one_leftCose
t _⟩) = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset`：τ_symm_apply_fromCose
t : Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.τ_apply_infinity`：τ_apply_infinity : τ ∞ = fr
omCoset ⟨f.hom.range, 1, one_leftCoset _⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem h_apply_fromCoset (x : B) :
    (h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
      fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp [-MonoidHom.coe_range, τ_symm_apply_fromCoset, g_apply_infinity, τ_apply_infinity]
/-
**GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset'** 是 Mathlib 中的一个定理，位于命名空间 `GrpCa
t.SurjectiveOfEpiAuxs`。
形式化陈述：h_apply_fromCoset' (x : B) (b : B) (hb : b in f.hom.range) : h x (fromCose
t ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩
参数：x : B；b : B；hb : b in f.hom.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset`：h_apply_fromCoset (x : B) 
: (h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = fromCoset ⟨f.hom.range, 
1, one_leftCoset _⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range`：fromCoset_eq_of_me
m_range {b : B} (hb : b in f.hom.range) : fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ =
 fromCoset ⟨f.hom.range, 1, one_leftCoset …
-/
theorem h_apply_fromCoset' (x : B) (b : B) (hb : b ∈ f.hom.range) :
    h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
  (fromCoset_eq_of_mem_range _ hb).symm ▸ h_apply_fromCoset f x
/-
**GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range** 是 Mathlib 中的一个定理，位于命名
空间 `GrpCat.SurjectiveOfEpiAuxs`。
形式化陈述：h_apply_fromCoset_nin_range (x : B) (hx : x in f.hom.range) (b : B) (hb : 
b ∉ f.hom.range) : h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b
) • ↑f.hom.range, x * b, rfl⟩
参数：x : B；hx : x in f.hom.range；b : B；hb : b ∉ f.hom.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_swap`：symm_swap (a b : α) : (swap a b).symm = swap a b
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range`：fromCoset_ne_of_ni
n_range {b : B} (hb : b ∉ f.hom.range) : fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ !=
 fromCoset ⟨f.hom.range, 1, one_leftCoset …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `leftCoset_assoc`：leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (
a * b) • s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
theorem h_apply_fromCoset_nin_range (x : B) (hx : x ∈ f.hom.range) (b : B) (hb : b ∉ f.hom.range) :
    h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.hom.range, x * b, rfl⟩ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [tau, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap,
    @Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.hom.range, b, rfl⟩) (fromCoset_ne_of_nin_range _ hb) (by simp)]
  simp only [g_apply_fromCoset, leftCoset_assoc]
  refine Equiv.swap_apply_of_ne_of_ne (fromCoset_ne_of_nin_range _ fun r => hb ?_) (by simp)
  convert! Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, inv_mul_cancel, one_mul]
/-
**GrpCat.SurjectiveOfEpiAuxs.agree** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.SurjectiveO
fEpiAuxs`。
形式化陈述：agree : f.hom.range = { x | h x = g x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset`：g_apply_fromCoset (x : B) 
(y : X) : g x (fromCoset y) = fromCoset ⟨x • ↑y, by obtain ⟨z, hz⟩
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset'`：h_apply_fromCoset' (x : B
) (b : B) (hb : b in f.hom.range) : h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = 
fromCoset ⟨b • ↑f.hom.range, b, rfl…
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range`：fromCoset_eq_of_me
m_range {b : B} (hb : b in f.hom.range) : fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ =
 fromCoset ⟨f.hom.range, 1, one_leftCoset …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range`：h_apply_fromCose
t_nin_range (x : B) (hx : x in f.hom.range) (b : B) (hb : b ∉ f.hom.range) : h x
 (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fro…
· 使用定理 `leftCoset_assoc`：leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (
a * b) • s
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity`：g_apply_infinity (x : B) : 
(g x) ∞ = ∞
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.h_apply_infinity`：h_apply_infinity (x : B) (h
x : x in f.hom.range) : (h x) ∞ = ∞
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range`：fromCoset_ne_of_ni
n_range {b : B} (hb : b ∉ f.hom.range) : fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ !=
 fromCoset ⟨f.hom.range, 1, one_leftCoset …
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem agree : f.hom.range = { x | h x = g x } := by
  refine Set.ext fun b => ⟨?_, fun hb : h b = g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_fromCoset]
      by_cases m : y ∈ f.hom.range
      · rw [h_apply_fromCoset' _ _ _ m, fromCoset_eq_of_mem_range _ m]
        change fromCoset _ = fromCoset ⟨f a • (y • _), _⟩
        simp only [← fromCoset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), smul_smul]
      · rw [h_apply_fromCoset_nin_range f (f a) ⟨_, rfl⟩ _ m]
        simp only [leftCoset_assoc]
    · rw [g_apply_infinity, h_apply_infinity f (f a) ⟨_, rfl⟩]
  · have eq1 : (h b) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
        fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
      change ((τ).symm.trans (g b)).trans τ _ = _
      dsimp [tau]
      simp [g_apply_infinity f]
    have eq2 :
        g b (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
      rfl
    exact (fromCoset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, DFunLike.congr_fun hb])
/-
**GrpCat.SurjectiveOfEpiAuxs.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Surjectiv
eOfEpiAuxs`。
形式化陈述：comp_eq : (f ≫ ofHom g) = f ≫ ofHom h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GrpCat.hom_ext`：hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom
) : f = g
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.agree`：agree : f.hom.range = { x | h x = g x 
}
-/
theorem comp_eq : (f ≫ ofHom g) = f ≫ ofHom h := by
  ext a
  simp only [hom_comp, hom_ofHom, MonoidHom.coe_comp, Function.comp_apply]
  have : f a ∈ { b | h b = g b } := by
    rw [← agree]
    use a
  rw [this]

set_option backward.isDefEq.respectTransparency.types false in
/-
**GrpCat.SurjectiveOfEpiAuxs.g_ne_h** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat.Surjective
OfEpiAuxs`。
形式化陈述：g_ne_h (x : B) (hx : x ∉ f.hom.range) : g != h
参数：x : B；hx : x ∉ f.hom.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range`：fromCoset_ne_of_ni
n_range {b : B} (hb : b ∉ f.hom.range) : fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ !=
 fromCoset ⟨f.hom.range, 1, one_leftCoset …
· 使用定理 `one_leftCoset`：one_leftCoset : (1 : α) • s = s
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.XWithInfinity.fromCoset.injEq`：∀ {A B : GrpCa
t} {f : A ⟶ B} (a a_1 : ↑(Set.range fun x => x • ↑(GrpCat.Hom.hom f).range)),   
(GrpCat.SurjectiveOfEpiAuxs.XWithInfinity.from…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
-/
theorem g_ne_h (x : B) (hx : x ∉ f.hom.range) : g ≠ h := by
  intro r
  apply fromCoset_ne_of_nin_range _ hx
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  simpa [g_apply_fromCoset, «h», tau, g_apply_infinity] using r

end SurjectiveOfEpiAuxs

/-
**GrpCat.surjective_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：surjective_of_epi [Epi f] : Function.Surjective f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.g_ne_h`：g_ne_h (x : B) (hx : x ∉ f.hom.range)
 : g != h
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `GrpCat.SurjectiveOfEpiAuxs.comp_eq`：comp_eq : (f ≫ ofHom g) = f ≫ ofHom 
h
-/
theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  dsimp [Function.Surjective]
  by_contra! ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      (congr_arg GrpCat.Hom.hom ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f)))
/-
**GrpCat.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：epi_iff_surjective : Epi f ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GrpCat.surjective_of_epi`：surjective_of_epi [Epi f] : Function.Surjectiv
e f
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩
/-
**GrpCat.epi_iff_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `GrpCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surject
ive f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subgroup.eq_top_iff'`：eq_top_iff' : H = ⊤ ↔ forall x : G, x in H
-/
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.hom.range).symm

end GrpCat

namespace AddGrpCat


variable {A B : AddGrpCat.{u}} (f : A ⟶ B)

/-
**AddGrpCat.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AddGrpCat`。
形式化陈述：epi_iff_surjective : Epi f ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape`：∀ {C : T
ype u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GrpCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surject
ive f
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [GrpCat.epi_iff_surjective] at i1
/-
**AddGrpCat.epi_iff_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `AddGrpCat`。
形式化陈述：epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddGrpCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AddSubgroup.eq_top_iff'`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSu
bgroup G), H = ⊤ ↔ ∀ (x : G), x ∈ H
-/
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.hom.range).symm

end AddGrpCat

namespace GrpCat


variable {A B : GrpCat.{u}} (f : A ⟶ B)

@[to_additive AddGrpCat.forget_grp_preserves_mono]
/-
**GrpCat.forget_grp_preserves_mono** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
形式化陈述：forget_grp_preserves_mono : (forget GrpCat).PreservesMonomorphisms where p
reserves f e
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ofHom_mono_iff_injective`：ofHom_mono_iff_injective {X Y :
 Type u} (f : X -> Y) : Mono (ofHom f) ↔ Function.Injective f
· 使用定理 `GrpCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inject
ive f
-/
instance forget_grp_preserves_mono : (forget GrpCat).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddGrpCat.forget_grp_preserves_epi]
/-
**GrpCat.forget_grp_preserves_epi** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
形式化陈述：forget_grp_preserves_epi : (forget GrpCat).PreservesEpimorphisms where pre
serves f e
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ofHom_epi_iff_surjective`：ofHom_epi_iff_surjective {X Y :
 Type u} (f : X -> Y) : Epi (ofHom f) ↔ Function.Surjective f
· 使用定理 `GrpCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surject
ive f
-/
instance forget_grp_preserves_epi : (forget GrpCat).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

end GrpCat

namespace CommGrpCat


variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

@[to_additive]
/-
**CommGrpCat.ker_eq_bot_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ker_eq_bot_of_cancel`：ker_eq_bot_of_cancel {f : A ->* B} (h : 
forall u v : f.ker ->* A, f.comp u = f.comp v -> u = v) : f.ker = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.ext_iff`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : 
(X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
-/
theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 <| ConcreteCategory.ext h

@[to_additive]
/-
**CommGrpCat.mono_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGrpCat.ker_eq_bot_of_mono`：ker_eq_bot_of_mono [Mono f] : f.hom.ker =
 ⊥
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
-/
theorem mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f.hom).1 h⟩

@[to_additive]
/-
**CommGrpCat.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：mono_iff_injective : Mono f ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CommGrpCat.mono_iff_ker_eq_bot`：mono_iff_ker_eq_bot : Mono f ↔ f.hom.ker
 = ⊥
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f.hom

@[to_additive]
/-
**CommGrpCat.range_eq_top_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：range_eq_top_of_epi [Epi f] : f.hom.range = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.range_eq_top_of_cancel`：range_eq_top_of_cancel {f : A ->* B} (
h : forall u v : B ->* B ⧸ f.range, u.comp f = v.comp f -> u = v) : f.range = ⊤
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.ext_iff`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : 
(X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
-/
theorem range_eq_top_of_epi [Epi f] : f.hom.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h => ConcreteCategory.ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext h)

@[to_additive]
/-
**CommGrpCat.epi_iff_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGrpCat.range_eq_top_of_epi`：range_eq_top_of_epi [Epi f] : f.hom.rang
e = ⊤
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| show Function.Surjective f.hom from
      MonoidHom.range_eq_top.mp hf⟩

@[to_additive]
/-
**CommGrpCat.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：epi_iff_surjective : Epi f ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommGrpCat.epi_iff_range_eq_top`：epi_iff_range_eq_top : Epi f ↔ f.hom.ra
nge = ⊤
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, MonoidHom.range_eq_top]

@[to_additive AddCommGrpCat.forget_commGrp_preserves_mono]
/-
**CommGrpCat.forget_commGrp_preserves_mono** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat
`。
形式化陈述：forget_commGrp_preserves_mono : (forget CommGrpCat).PreservesMonomorphisms
 where preserves f e
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ofHom_mono_iff_injective`：ofHom_mono_iff_injective {X Y :
 Type u} (f : X -> Y) : Mono (ofHom f) ↔ Function.Injective f
· 使用定理 `CommGrpCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.In
jective f
-/
instance forget_commGrp_preserves_mono : (forget CommGrpCat).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective] at e

@[to_additive AddCommGrpCat.forget_commGrp_preserves_epi]
/-
**CommGrpCat.forget_commGrp_preserves_epi** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`
。
形式化陈述：forget_commGrp_preserves_epi : (forget CommGrpCat).PreservesEpimorphisms w
here preserves f e
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ofHom_epi_iff_surjective`：ofHom_epi_iff_surjective {X Y :
 Type u} (f : X -> Y) : Epi (ofHom f) ↔ Function.Surjective f
· 使用定理 `CommGrpCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Sur
jective f
-/
instance forget_commGrp_preserves_epi : (forget CommGrpCat).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective] at e

end CommGrpCat

end


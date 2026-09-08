/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Order.SuccPred.WithBot
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Constructible sets in the prime spectrum

This file provides tooling for manipulating constructible sets in the prime spectrum of a ring.

-/

@[expose] public section

open Finset Topology
open scoped Polynomial

namespace PrimeSpectrum
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (R) in
/-- The data of a basic constructible set `s` is a tuple `(f, g₁, ..., gₙ)` -/
@[ext]
/-
**PrimeSpectrum.BasicConstructibleSetData** 是 Mathlib 中的一个归纳类型，位于命名空间 `PrimeSpec
trum`。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a basic constructible set `s` is a tuple `(f, g₁, ..., gₙ)`
-/
structure BasicConstructibleSetData where
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `f`. -/
  protected f : R
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `n`. -/
  protected n : ℕ
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `g`. -/
  protected g : Fin n → R

namespace BasicConstructibleSetData

/-
**PrimeSpectrum.BasicConstructibleSetData.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpect
rum.BasicConstructibleSetData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DecidableEq (BasicConstructibleSetData R) := Classical.decEq _

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | φ x ∈ I} ∈ s}`. -/
@[simps]
/-
**PrimeSpectrum.BasicConstructibleSetData.map** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSp
ectrum.BasicConstructibleSetData`。
形式化陈述：map (φ : R ->+* S) (C : BasicConstructibleSetData R) : BasicConstructibleS
etData S where f
参数：φ : R ->+* S；C : BasicConstructibleSetData R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the data of the constructible set `s`, build the data of the constructible
 set
`{I | {x | φ x ∈ I} ∈ s}`.
-/
noncomputable def map (φ : R →+* S) (C : BasicConstructibleSetData R) :
    BasicConstructibleSetData S where
  f := φ C.f
  n := C.n
  g := φ ∘ C.g
/-
**PrimeSpectrum.BasicConstructibleSetData.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Prim
eSpectrum.BasicConstructibleSetData`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (C : PrimeSpectrum.BasicConstruct
ibleSetData R),   PrimeSpectrum.BasicConstructibleSetData.map (RingHom.id R) C =
 C
参数：C : PrimeSpectrum.BasicConstructibleSetData R；RingHom.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id (C : BasicConstructibleSetData R) : C.map (.id _) = C := by simp [map]
/-
**PrimeSpectrum.BasicConstructibleSetData.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Pri
meSpectrum.BasicConstructibleSetData`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], PrimeSpectrum.BasicConstructible
SetData.map (RingHom.id R) = id
参数：RingHom.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.BasicConstructibleSetData.map_id`：∀ {R : Type u_1} [inst :
 CommSemiring R] (C : PrimeSpectrum.BasicConstructibleSetData R),   PrimeSpectru
m.BasicConstructibleSetData.map (Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id' : map (.id R) = id := by ext : 1; simp
/-
**PrimeSpectrum.BasicConstructibleSetData.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Pr
imeSpectrum.BasicConstructibleSetData`。
形式化陈述：map_comp (φ : S ->+* T) (ψ : R ->+* S) (C : BasicConstructibleSetData R) :
 C.map (φ.comp ψ) = (C.map ψ).map φ
参数：φ : S ->+* T；ψ : R ->+* S；C : BasicConstructibleSetData R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (φ : S →+* T) (ψ : R →+* S) (C : BasicConstructibleSetData R) :
    C.map (φ.comp ψ) = (C.map ψ).map φ := by simp [map, Function.comp_def]
/-
**PrimeSpectrum.BasicConstructibleSetData.map_comp'** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum.BasicConstructibleSetData`。
形式化陈述：map_comp' (φ : S ->+* T) (ψ : R ->+* S) : map (φ.comp ψ) = map φ ∘ map ψ
参数：φ : S ->+* T；ψ : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimeSpectrum.BasicConstructibleSetData.map_comp`：map_comp (φ : S ->+* T
) (ψ : R ->+* S) (C : BasicConstructibleSetData R) : C.map (φ.comp ψ) = (C.map ψ
).map φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp' (φ : S →+* T) (ψ : R →+* S) : map (φ.comp ψ) = map φ ∘ map ψ := by
  ext : 1; simp [map_comp]

/-- Given the data of a basic constructible set `s`, namely a tuple `(f, g₁, ..., gₙ)` such that
`s = V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
/-
**PrimeSpectrum.BasicConstructibleSetData.toSet** 是 Mathlib 中的一个定义，位于命名空间 `Prime
Spectrum.BasicConstructibleSetData`。
形式化陈述：toSet (C : BasicConstructibleSetData R) : Set (PrimeSpectrum R)
参数：C : BasicConstructibleSetData R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the data of a basic constructible set `s`, namely a tuple `(f, g₁, ..., gₙ
)` such that
`s = V(g₁, ..., gₙ) \ V(f)`, return `s`.
-/
def toSet (C : BasicConstructibleSetData R) : Set (PrimeSpectrum R) :=
  zeroLocus (Set.range C.g) \ zeroLocus {C.f}

@[simp]
/-
**PrimeSpectrum.BasicConstructibleSetData.toSet_map** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum.BasicConstructibleSetData`。
形式化陈述：toSet_map (φ : R ->+* S) (C : BasicConstructibleSetData R) : (C.map φ).toS
et = comap φ ⁻¹' C.toSet
参数：φ : R ->+* S；C : BasicConstructibleSetData R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PrimeSpectrum.preimage_comap_zeroLocus`：preimage_comap_zeroLocus (s : Se
t R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSet_map (φ : R →+* S) (C : BasicConstructibleSetData R) :
    (C.map φ).toSet = comap φ ⁻¹' C.toSet := by simp [toSet, map, ← Set.range_comp]

end BasicConstructibleSetData

variable (R) in
/-- The data of a constructible set `s` in the prime spectrum of a ring is finitely many tuples
`(f, g₁, ..., gₙ)` such that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`.

To obtain `s` from its data, use `PrimeSpectrum.ConstructibleSetData.toSet`. -/
/-
**PrimeSpectrum.ConstructibleSetData** 是 Mathlib 中的一个缩写定义，位于命名空间 `PrimeSpectrum`
。
形式化陈述：ConstructibleSetData
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a constructible set `s` in the prime spectrum of a ring is finitely 
many tuples
`(f, g₁, ..., gₙ)` such that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`.

To obtain `s` from its data, use `PrimeSpectrum.ConstructibleSetData.toSet`.
-/
abbrev ConstructibleSetData := Finset (BasicConstructibleSetData R)

namespace ConstructibleSetData

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | f x ∈ I} ∈ s}`. -/
/-
**PrimeSpectrum.ConstructibleSetData.map** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectru
m.ConstructibleSetData`。
形式化陈述：map (φ : R ->+* S) (s : ConstructibleSetData R) : ConstructibleSetData S
参数：φ : R ->+* S；s : ConstructibleSetData R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the data of the constructible set `s`, build the data of the constructible
 set
`{I | {x | f x ∈ I} ∈ s}`.
-/
noncomputable def map (φ : R →+* S) (s : ConstructibleSetData R) : ConstructibleSetData S :=
  s.image (.map φ)

@[simp]
/-
**PrimeSpectrum.ConstructibleSetData.map_id** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum.ConstructibleSetData`。
形式化陈述：map_id (s : ConstructibleSetData R) : s.map (.id _) = s
参数：s : ConstructibleSetData R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.BasicConstructibleSetData.map_id'`：∀ {R : Type u_1} [inst 
: CommSemiring R], PrimeSpectrum.BasicConstructibleSetData.map (RingHom.id R) = 
id
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (s : ConstructibleSetData R) : s.map (.id _) = s := by simp [map]
/-
**PrimeSpectrum.ConstructibleSetData.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSp
ectrum.ConstructibleSetData`。
形式化陈述：map_comp (f : S ->+* T) (g : R ->+* S) (s : ConstructibleSetData R) : s.ma
p (f.comp g) = (s.map g).map f
参数：f : S ->+* T；g : R ->+* S；s : ConstructibleSetData R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PrimeSpectrum.BasicConstructibleSetData.map_comp'`：map_comp' (φ : S ->+*
 T) (ψ : R ->+* S) : map (φ.comp ψ) = map φ ∘ map ψ
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (f : S →+* T) (g : R →+* S) (s : ConstructibleSetData R) :
    s.map (f.comp g) = (s.map g).map f := by
  simp [map, image_image, Function.comp_def, BasicConstructibleSetData.map_comp']

/-- Given the data of a constructible set `s`, namely finitely many tuples `(f, g₁, ..., gₙ)` such
that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
/-
**PrimeSpectrum.ConstructibleSetData.toSet** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpect
rum.ConstructibleSetData`。
形式化陈述：toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R)
参数：S : ConstructibleSetData R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the data of a constructible set `s`, namely finitely many tuples `(f, g₁, 
..., gₙ)` such
that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`, return `s`.
-/
def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) := ⋃ C ∈ S, C.toSet

@[simp]
/-
**PrimeSpectrum.ConstructibleSetData.toSet_map** 是 Mathlib 中的一个引理，位于命名空间 `PrimeS
pectrum.ConstructibleSetData`。
形式化陈述：toSet_map (f : R ->+* S) (s : ConstructibleSetData R) : (s.map f).toSet = 
comap f ⁻¹' s.toSet
参数：f : R ->+* S；s : ConstructibleSetData R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.set_biUnion_finset_image`：set_biUnion_finset_image {f : γ -> α} {
g : α -> Set β} {s : Finset γ} : ⋃ x in s.image f, g x = ⋃ y in s, g (f y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `PrimeSpectrum.BasicConstructibleSetData.toSet_map`：toSet_map (φ : R ->+*
 S) (C : BasicConstructibleSetData R) : (C.map φ).toSet = comap φ ⁻¹' C.toSet
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSet_map (f : R →+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp

/-- The degree bound on a constructible set for Chevalley's theorem for the inclusion `R ↪ R[X]`. -/
/-
**PrimeSpectrum.ConstructibleSetData.degBound** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSp
ectrum.ConstructibleSetData`。
形式化陈述：degBound (S : ConstructibleSetData R[X]) : Nat
参数：S : ConstructibleSetData R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree bound on a constructible set for Chevalley's theorem for the inclusio
n `R ↪ R[X]`.
-/
def degBound (S : ConstructibleSetData R[X]) : ℕ := S.sup fun C ↦ ∑ i, (C.g i).degree.succ
/-
**PrimeSpectrum.ConstructibleSetData.isConstructible_toSet** 是 Mathlib 中的一个引理，位于
命名空间 `PrimeSpectrum.ConstructibleSetData`。
形式化陈述：isConstructible_toSet (S : ConstructibleSetData R) : IsConstructible S.toS
et
参数：S : ConstructibleSetData R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsConstructible.biUnion`：∀ {X : Type u_2} [inst : TopologicalSp
ace X] {ι : Type u_4} {f : ι → Set X} {t : Set ι},   t.Finite → (∀ i ∈ t, Topolo
gy.IsConstructible (f …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Topology.IsConstructible.sdiff`：∀ {X : Type u_2} [inst : TopologicalSpac
e X] {s t : Set X},   Topology.IsConstructible s → Topology.IsConstructible t → 
Topology.IsConstruct…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.isConstructible_compl`：∀ {X : Type u_2} [inst : TopologicalSpac
e X] {s : Set X}, Topology.IsConstructible sᶜ ↔ Topology.IsConstructible s
· 使用定理 `IsRetrocompact.isConstructible`：∀ {X : Type u_2} [inst : TopologicalSpac
e X] {U : Set X}, IsOpen U → IsRetrocompact U → Topology.IsConstructible U
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
· 使用引理 `PrimeSpectrum.isRetrocompact_zeroLocus_compl`：isRetrocompact_zeroLocus_c
ompl {s : Set R} (hs : s.Finite) : IsRetrocompact (zeroLocus s)ᶜ
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
lemma isConstructible_toSet (S : ConstructibleSetData R) :
    IsConstructible S.toSet := by
  refine .biUnion S.finite_toSet fun _ _ ↦ .sdiff ?_ ?_
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_range _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_singleton _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl

end ConstructibleSetData

/-
**PrimeSpectrum.exists_constructibleSetData_iff** 是 Mathlib 中的一个引理，位于命名空间 `Prime
Spectrum`。
形式化陈述：exists_constructibleSetData_iff {s : Set (PrimeSpectrum R)} : (exists S : 
ConstructibleSetData R, S.toSet = s) ↔ IsConstructible s
参数：PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.ConstructibleSetData.isConstructible_toSet`：isConstructibl
e_toSet (S : ConstructibleSetData R) : IsConstructible S.toSet
· 使用定理 `Topology.IsConstructible.induction_of_isTopologicalBasis`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [CompactSpace X] {P : (s : Set X) → Topology.IsCo
nstructible s → Prop}   [inst_2 : QuasiSeparat…
· 使用定理 `PrimeSpectrum.instQuasiSeparatedSpace`：∀ {R : Type u} [inst : CommSemiri
ng R], QuasiSeparatedSpace (PrimeSpectrum R)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `PrimeSpectrum.isCompact_basicOpen`：isCompact_basicOpen (f : R) : IsCompa
ct (basicOpen f : Set (PrimeSpectrum R))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `compl_sdiff_compl`：compl_sdiff_compl : xᶜ \ yᶜ = y \ x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.exists_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∃ a, q (e a)) ↔ ∃ b, q b
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Set.biUnion_union`：biUnion_union (s t : Set α) (u : α -> Set β) : ⋃ x in
 s union t, u x = (⋃ x in s, u x) union ⋃ x in t, u x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_constructibleSetData_iff {s : Set (PrimeSpectrum R)} :
    (∃ S : ConstructibleSetData R, S.toSet = s) ↔ IsConstructible s := by
  refine ⟨fun ⟨S, H⟩ ↦ H ▸ S.isConstructible_toSet, fun H ↦ ?_⟩
  induction s, H using IsConstructible.induction_of_isTopologicalBasis
      _ (isTopologicalBasis_basic_opens (R := R)) with
  | isCompact_basis i => exact isCompact_basicOpen _
  | sdiff i s hs =>
    have : Finite s := hs
    refine ⟨{⟨i, Nat.card s, fun i ↦ ((Finite.equivFin s).symm i).1⟩}, ?_⟩
    simp only [ConstructibleSetData.toSet, Finset.mem_singleton, BasicConstructibleSetData.toSet,
      Set.iUnion_iUnion_eq_left, basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂,
        compl_sdiff_compl, ← zeroLocus_iUnion₂, Set.biUnion_of_singleton]
    congr! 2
    ext
    simp [← (Finite.equivFin s).exists_congr_right, -Nat.card_coe_set_eq]
  | union s hs t ht Hs Ht =>
    obtain ⟨S, rfl⟩ := Hs
    obtain ⟨T, rfl⟩ := Ht
    refine ⟨S ∪ T, ?_⟩
    simp only [ConstructibleSetData.toSet, Set.biUnion_union, ← Finset.mem_coe, Finset.coe_union]

universe u in
@[stacks 00F8 "without the finite presentation part"]
-- TODO: show that the constructed `f` is of finite presentation
/-
**PrimeSpectrum.exists_range_eq_of_isConstructible** 是 Mathlib 中的一个引理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：exists_range_eq_of_isConstructible {R : Type u} [CommRing R] {s : Set (Pri
meSpectrum R)} (hs : IsConstructible s) : exists (S : Type u) (_ : CommRing S) (
f : R ->+* S), Set.range (comap f) = s
参数：PrimeSpectrum R；hs : IsConstructible s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimeSpectrum.exists_constructibleSetData_iff`：exists_constructibleSetDa
ta_iff {s : Set (PrimeSpectrum R)} : (exists S : ConstructibleSetData R, S.toSet
 = s) ↔ IsConstructible s
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.iUnion_range_comap_comp_evalRingHom`：iUnion_range_comap_co
mp_evalRingHom {ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)] [Finite ι
] {S : Type*} [CommRing S] (f : S ->+* …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `PrimeSpectrum.ConstructibleSetData.toSet.eq_1`：∀ {R : Type u_1} [inst : 
CommSemiring R] (S : PrimeSpectrum.ConstructibleSetData R), S.toSet = ⋃ C ∈ S, C
.toSet
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用引理 `PrimeSpectrum.comap_basicOpen`：comap_basicOpen (f : R ->+* S) (x : R) : 
TopologicalSpace.Opens.comap ⟨comap f, continuous_comap f⟩ (basicOpen x) = basic
Open (f x)
· 使用定理 `TopologicalSpace.Opens.coe_comap`：coe_comap (f : C(α, β)) (U : Opens β) 
: ↑(comap f U) = f ⁻¹' U
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `range_comap_of_surjective`：range_comap_of_surjective (hf : Surjective f)
 : Set.range (comap f) = zeroLocus (ker f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `PrimeSpectrum.BasicConstructibleSetData.toSet.eq_1`：∀ {R : Type u_1} [in
st : CommSemiring R] (C : PrimeSpectrum.BasicConstructibleSetData R),   C.toSet 
= PrimeSpectrum.zeroLocus (Set.range C.g…
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
-/
lemma exists_range_eq_of_isConstructible {R : Type u} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : IsConstructible s) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S), Set.range (comap f) = s := by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  refine ⟨Π i : s, Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f),
    inferInstance, algebraMap _ _, ?_⟩
  rw [← iUnion_range_comap_comp_evalRingHom, ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  let I := Ideal.span (Set.range C.1.g)
  let f := Ideal.Quotient.mk I C.1.f
  trans comap (Ideal.Quotient.mk I) '' (Set.range (comap (algebraMap _ (Localization.Away f))))
  · rw [← Set.range_comp]; rfl
  · rw [localization_away_comap_range _ f, ← comap_basicOpen, TopologicalSpace.Opens.coe_comap,
      ContinuousMap.coe_mk, Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, BasicConstructibleSetData.toSet,
      Set.sdiff_eq_compl_inter, basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, zeroLocus_span]

@[stacks 00I0 "(1)"]
/-
**PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible** 是 Mat
hlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isClosed_of_stableUnderSpecialization_of_isConstructible {R : Type*} [Comm
Ring R] {s : Set (PrimeSpectrum R)} (hs : StableUnderSpecialization s) (hs' : Is
Constructible s) : IsClosed s
参数：PrimeSpectrum R；hs : StableUnderSpecialization s；hs' : IsConstructible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.exists_range_eq_of_isConstructible`：exists_range_eq_of_isC
onstructible {R : Type u} [CommRing R] {s : Set (PrimeSpectrum R)} (hs : IsConst
ructible s) : exists (S : Type u) (_ :…
· 使用引理 `PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`：isClosed_rang
e_of_stableUnderSpecialization (hf : StableUnderSpecialization (Set.range (comap
 f))) : IsClosed (Set.range (comap f))
-/
lemma isClosed_of_stableUnderSpecialization_of_isConstructible {R : Type*} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderSpecialization s) (hs' : IsConstructible s) :
    IsClosed s := by
  obtain ⟨S, _, f, rfl⟩ := exists_range_eq_of_isConstructible hs'
  exact isClosed_range_of_stableUnderSpecialization _ hs

@[stacks 00I0 "(1)"]
/-
**PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible** 是 Mathl
ib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：isOpen_of_stableUnderGeneralization_of_isConstructible {R : Type*} [CommRi
ng R] {s : Set (PrimeSpectrum R)} (hs : StableUnderGeneralization s) (hs' : IsCo
nstructible s) : IsOpen s
参数：PrimeSpectrum R；hs : StableUnderGeneralization s；hs' : IsConstructible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用引理 `PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`：
isClosed_of_stableUnderSpecialization_of_isConstructible {R : Type*} [CommRing R
] {s : Set (PrimeSpectrum R)} (hs : StableUnderSpecializatio…
· 使用定理 `StableUnderGeneralization.compl`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {s : Set X}, StableUnderGeneralization s → StableUnderSpecialization sᶜ
· 使用定理 `Topology.IsConstructible.compl`：∀ {X : Type u_2} [inst : TopologicalSpac
e X] {s : Set X}, Topology.IsConstructible s → Topology.IsConstructible sᶜ
-/
lemma isOpen_of_stableUnderGeneralization_of_isConstructible {R : Type*} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderGeneralization s) (hs' : IsConstructible s) :
    IsOpen s := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stableUnderSpecialization_of_isConstructible hs.compl hs'.compl

end PrimeSpectrum


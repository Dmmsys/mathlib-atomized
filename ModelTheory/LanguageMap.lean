/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.ModelTheory.Basic

/-!
# Language Maps

Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language.LHom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
- A `FirstOrder.Language.LEquiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
- `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
  `A : Set M`, `L.withConstants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum
  hypothesis*][flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]

-/

@[expose] public section

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
/-
**FirstOrder.Language.LHom** 是 Mathlib 中的一个结构，位于命名空间 `FirstOrder.Language`。
形式化陈述：LHom where /-- The mapping of functions -/ onFunction : forall ⦃n⦄, L.Func
tions n -> L'.Functions n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language homomorphism maps the symbols of one language to symbols of another.
-/
structure LHom where
  /-- The mapping of functions -/
  onFunction : ∀ ⦃n⦄, L.Functions n → L'.Functions n := by
    exact fun {n} => isEmptyElim
  /-- The mapping of relations -/
  onRelation : ∀ ⦃n⦄, L.Relations n → L'.Relations n := by
    exact fun {n} => isEmptyElim

@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " →ᴸ " => LHom

-- \^L
variable {L L'}

namespace LHom

variable (ϕ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
@[instance_reducible]
/-
**FirstOrder.Language.LHom.reduct** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LHom`。
形式化陈述：reduct (M : Type*) [L'.Structure M] : L.Structure M where funMap f xs
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulls a structure back along a language map.
-/
def reduct (M : Type*) [L'.Structure M] : L.Structure M where
  funMap f xs := funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

/-- The identity language homomorphism. -/
@[simps]
/-
**FirstOrder.Language.LHom.id** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.LHo
m`。
形式化陈述：(L : FirstOrder.Language) → L →ᴸ L
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity language homomorphism.
-/
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun _n => id, fun _n => id⟩
/-
**FirstOrder.Language.LHom.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.LHom`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
/-
**FirstOrder.Language.LHom.sumInl** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LHom`。
形式化陈述：{L : FirstOrder.Language} → {L' : FirstOrder.Language} → L →ᴸ L.sum L'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the left factor into the sum of two languages.
-/
protected def sumInl : L →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
/-
**FirstOrder.Language.LHom.sumInr** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LHom`。
形式化陈述：{L : FirstOrder.Language} → {L' : FirstOrder.Language} → L' →ᴸ L.sum L'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the right factor into the sum of two languages.
-/
protected def sumInr : L' →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
/-
**FirstOrder.Language.LHom.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.LHom`。
形式化陈述：(L : FirstOrder.Language) → (L' : FirstOrder.Language) → [L.IsAlgebraic] →
 [L.IsRelational] → L →ᴸ L'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of an empty language into any other language.
-/
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' where

variable {L L'} {L'' : Language}

@[ext]
/-
**FirstOrder.Language.LHom.funext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language
.LHom`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} {F G : L →ᴸ L'},   
F.onFunction = G.onFunction → F.onRelation = G.onRelation → F = G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.mk.injEq`：∀ {L : FirstOrder.Language} {L' : Fir
stOrder.Language}   (onFunction : autoParam (⦃n : ℕ⦄ → L.Functions n → L'.Functi
ons n) FirstOrder.Langu…
-/
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel
/-
**FirstOrder.Language.LHom.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.LHom`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- The composition of two language homomorphisms. -/
@[simps]
/-
**FirstOrder.Language.LHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.L
Hom`。
形式化陈述：comp (g : L' ->ᴸ L'') (f : L ->ᴸ L') : L ->ᴸ L''
参数：g : L' ->ᴸ L''；f : L ->ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two language homomorphisms.
-/
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

-- added ᴸ to avoid clash with function composition
@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp

@[simp]
/-
**FirstOrder.Language.LHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.LHom`。
形式化陈述：id_comp (F : L ->ᴸ L') : LHom.id L' ∘ᴸ F = F
参数：F : L ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F := by
  cases F
  rfl

@[simp]
/-
**FirstOrder.Language.LHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.LHom`。
形式化陈述：comp_id (F : L ->ᴸ L') : F ∘ᴸ LHom.id L = F
参数：F : L ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F := by
  cases F
  rfl
/-
**FirstOrder.Language.LHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.LHom`。
形式化陈述：comp_assoc {L3 : Language} (F : L'' ->ᴸ L3) (G : L' ->ᴸ L'') (H : L ->ᴸ L'
) : F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H)
参数：F : L'' ->ᴸ L3；G : L' ->ᴸ L''；H : L ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {L3 : Language} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

section SumElim

variable (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
/-
**FirstOrder.Language.LHom.sumElim** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.LHom`。
形式化陈述：{L : FirstOrder.Language} →   {L' : FirstOrder.Language} → (L →ᴸ L') → {L'
' : FirstOrder.Language} → (L'' →ᴸ L') → (L.sum L'' →ᴸ L')
参数：L →ᴸ L'；L'' →ᴸ L'；L.sum L'' →ᴸ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language map defined on two factors of a sum.
-/
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _n := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f
/-
**FirstOrder.Language.LHom.sumElim_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：sumElim_comp_inl (ψ : L'' ->ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ
参数：ψ : L'' ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem sumElim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
/-
**FirstOrder.Language.LHom.sumElim_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：sumElim_comp_inr (ψ : L'' ->ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ
参数：ψ : L'' ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem sumElim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
/-
**FirstOrder.Language.LHom.sumElim_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.LHom`。
形式化陈述：sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.elim_inl_inr`：∀ {α : Type u_1} {β : Type u_2}, Sum.elim Sum.inl Sum.
inr = id
-/
theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)
/-
**FirstOrder.Language.LHom.comp_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.LHom`。
形式化陈述：comp_sumElim {L3 : Language} (θ : L' ->ᴸ L3) : θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ)
.sumElim (θ ∘ᴸ ψ)
参数：θ : L' ->ᴸ L3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.comp_elim`：∀ {γ : Sort u_1} {δ : Sort u_2} {α : Type u_3} {β : Type 
u_4} (f : γ → δ) (g : α → γ) (h : β → γ),   f ∘ Sum.elim g h = Sum.elim (f ∘ g) 
(f …
-/
theorem comp_sumElim {L3 : Language} (θ : L' →ᴸ L3) :
    θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
/-
**FirstOrder.Language.LHom.sumMap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LHom`。
形式化陈述：sumMap : L.sum L₁ ->ᴸ L'.sum L₂ where onFunction _n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between two sum-languages induced by maps on the two factors.
-/
def sumMap : L.sum L₁ →ᴸ L'.sum L₂ where
  onFunction _n := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]
/-
**FirstOrder.Language.LHom.sumMap_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.LHom`。
形式化陈述：sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]
/-
**FirstOrder.Language.LHom.sumMap_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.LHom`。
形式化陈述：sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap

/-- A language homomorphism is injective when all the maps between symbol types are. -/
/-
**FirstOrder.Language.LHom.Injective** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Lan
guage.LHom`。
形式化陈述：{L : FirstOrder.Language} → {L' : FirstOrder.Language} → (L →ᴸ L') → Prop
参数：L →ᴸ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language homomorphism is injective when all the maps between symbol types are.
-/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective fun f : L.Functions n => onFunction ϕ f
  onRelation {n} : Function.Injective fun R : L.Relations n => onRelation ϕ R

/-- Pulls an `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily. -/
@[instance_reducible]
/-
**FirstOrder.Language.LHom.defaultExpansion** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：defaultExpansion (ϕ : L ->ᴸ L') [forall (n) (f : L'.Functions n), Decidabl
e (f in Set.range fun f : L.Functions n => onFunction ϕ f)] [forall (n) (r : L'.
Relations n), Decidable (r in Set.range fun r : L.Relations n => onRelation ϕ r)
] (M : Type*) [Inhabited M] [L.Structure M] : L'.Structure M where funMap {n} f 
xs
参数：ϕ : L ->ᴸ L'；n；f : L'.Functions n；f in Set.range fun f : L.Functions n => onF
unction ϕ f；n；r : L'.Relations n；r in Set.range fun r : L.Relations n => onRelat
ion ϕ r；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulls an `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily.
-/
noncomputable def defaultExpansion (ϕ : L →ᴸ L')
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => onFunction ϕ f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => onRelation ϕ r)]
    (M : Type*) [Inhabited M] [L.Structure M] : L'.Structure M where
  funMap {n} f xs :=
    if h' : f ∈ Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {n} r xs :=
    if h' : r ∈ Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.choose xs
    else default

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
/-
**FirstOrder.Language.LHom.IsExpansionOn** 是 Mathlib 中的一个类，位于命名空间 `FirstOrder.La
nguage.LHom`。
形式化陈述：IsExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : Prop where ma
p_onFunction : forall {n} (f : L.Functions n) (x : Fin n -> M), funMap (ϕ.onFunc
tion f) x = funMap f x
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language homomorphism is an expansion on a structure if it commutes with the i
nterpretation of
all symbols on that structure.
-/
class IsExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction :
    ∀ {n} (f : L.Functions n) (x : Fin n → M), funMap (ϕ.onFunction f) x = funMap f x := by
      exact fun {n} => isEmptyElim
  map_onRelation :
    ∀ {n} (R : L.Relations n) (x : Fin n → M), RelMap (ϕ.onRelation R) x = RelMap R x := by
      exact fun {n} => isEmptyElim

@[simp]
/-
**FirstOrder.Language.LHom.map_onFunction** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.LHom`。
形式化陈述：map_onFunction {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansion
On M] {n} (f : L.Functions n) (x : Fin n -> M) : funMap (ϕ.onFunction f) x = fun
Map f x
参数：f : L.Functions n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.IsExpansionOn.map_onFunction`：∀ {L : FirstOrder
.Language} {L' : FirstOrder.Language} {ϕ : L →ᴸ L'} {M : Type u_1} {inst : L.Str
ucture M}   {inst_1 : L'.Structure M} [self…
-/
theorem map_onFunction {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (f : L.Functions n) (x : Fin n → M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x

@[simp]
/-
**FirstOrder.Language.LHom.map_onRelation** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.LHom`。
形式化陈述：map_onRelation {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansion
On M] {n} (R : L.Relations n) (x : Fin n -> M) : RelMap (ϕ.onRelation R) x = Rel
Map R x
参数：R : L.Relations n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.IsExpansionOn.map_onRelation`：∀ {L : FirstOrder
.Language} {L' : FirstOrder.Language} {ϕ : L →ᴸ L'} {M : Type u_1} {inst : L.Str
ucture M}   {inst_1 : L'.Structure M} [self…
-/
theorem map_onRelation {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (R : L.Relations n) (x : Fin n → M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_onRelation R x
/-
**FirstOrder.Language.LHom.id_isExpansionOn** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：id_isExpansionOn (M : Type*) [L.Structure M] : IsExpansionOn (LHom.id L) M
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance id_isExpansionOn (M : Type*) [L.Structure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
/-
**FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.LHom`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} (M : Type u_1) [ins
t : L.Structure M] [inst_1 : L'.Structure M]   [inst_2 : L.IsAlgebraic] [inst_3 
: L.IsRelational], (FirstOrder.Language.LHom.ofIsEmpty L L').IsExpansionOn M
参数：M : Type u_1；FirstOrder.Language.LHom.ofIsEmpty L L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ofIsEmpty_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]
    [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M where
/-
**FirstOrder.Language.LHom.sumElim_isExpansionOn** 是 Mathlib 中的一个实例，位于命名空间 `Firs
tOrder.Language.LHom`。
形式化陈述：sumElim_isExpansionOn {L'' : Language} (ψ : L'' ->ᴸ L') (M : Type*) [L.Str
ucture M] [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionO
n M] : (ϕ.sumElim ψ).IsExpansionOn M
参数：ψ : L'' ->ᴸ L'；M : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.LHom.sumElim_onFunction`：∀ {L : FirstOrder.Language}
 {L' : FirstOrder.Language} (ϕ : L →ᴸ L') {L'' : FirstOrder.Language} (ψ : L'' →
ᴸ L')   (_n : ℕ) (a : L.Functions…
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FirstOrder.Language.LHom.sumElim_onRelation`：∀ {L : FirstOrder.Language}
 {L' : FirstOrder.Language} (ϕ : L →ᴸ L') {L'' : FirstOrder.Language} (ψ : L'' →
ᴸ L')   (_n : ℕ) (a : L.Relations…
· 使用定理 `FirstOrder.Language.LHom.map_onRelation`：map_onRelation {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (R : L.Relations n) (x : Fi
n n -> M) : RelMap (ϕ.onRelat…
-/
instance sumElim_isExpansionOn {L'' : Language} (ψ : L'' →ᴸ L') (M : Type*) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩
/-
**FirstOrder.Language.LHom.sumMap_isExpansionOn** 是 Mathlib 中的一个实例，位于命名空间 `First
Order.Language.LHom`。
形式化陈述：sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ ->ᴸ L₂) (M : Type*) [L.Str
ucture M] [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M]
 [ψ.IsExpansionOn M] : (ϕ.sumMap ψ).IsExpansionOn M
参数：ψ : L₁ ->ᴸ L₂；M : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.LHom.sumMap_onFunction`：∀ {L : FirstOrder.Language} 
{L' : FirstOrder.Language} (ϕ : L →ᴸ L') {L₁ : FirstOrder.Language}   {L₂ : Firs
tOrder.Language} (ψ : L₁ →ᴸ L₂) …
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FirstOrder.Language.LHom.sumMap_onRelation`：∀ {L : FirstOrder.Language} 
{L' : FirstOrder.Language} (ϕ : L →ᴸ L') {L₁ : FirstOrder.Language}   {L₂ : Firs
tOrder.Language} (ψ : L₁ →ᴸ L₂) …
· 使用定理 `FirstOrder.Language.LHom.map_onRelation`：map_onRelation {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (R : L.Relations n) (x : Fi
n n -> M) : RelMap (ϕ.onRelat…
-/
instance sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type*) [L.Structure M]
    [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩
/-
**FirstOrder.Language.LHom.sumInl_isExpansionOn** 是 Mathlib 中的一个实例，位于命名空间 `First
Order.Language.LHom`。
形式化陈述：sumInl_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : (LHom.
sumInl : L ->ᴸ L.sum L').IsExpansionOn M
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sumInl_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩
/-
**FirstOrder.Language.LHom.sumInr_isExpansionOn** 是 Mathlib 中的一个实例，位于命名空间 `First
Order.Language.LHom`。
形式化陈述：sumInr_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : (LHom.
sumInr : L' ->ᴸ L.sum L').IsExpansionOn M
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sumInr_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInr : L' →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

@[simp]
/-
**FirstOrder.Language.LHom.funMap_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.LHom`。
形式化陈述：funMap_sumInl [(L.sum L').Structure M] [(LHom.sumInl : L ->ᴸ L.sum L').IsE
xpansionOn M] {n} {f : L.Functions n} {x : Fin n -> M} : @funMap (L.sum L') M _ 
n (Sum.inl f) x = funMap f x
参数：L.sum L'；LHom.sumInl : L ->ᴸ L.sum L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
-/
theorem funMap_sumInl [(L.sum L').Structure M] [(LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L.sum L') M _ n (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L →ᴸ L.sum L').map_onFunction f x

@[simp]
/-
**FirstOrder.Language.LHom.funMap_sumInr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.LHom`。
形式化陈述：funMap_sumInr [(L'.sum L).Structure M] [(LHom.sumInr : L ->ᴸ L'.sum L).IsE
xpansionOn M] {n} {f : L.Functions n} {x : Fin n -> M} : @funMap (L'.sum L) M _ 
n (Sum.inr f) x = funMap f x
参数：L'.sum L；LHom.sumInr : L ->ᴸ L'.sum L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
-/
theorem funMap_sumInr [(L'.sum L).Structure M] [(LHom.sumInr : L →ᴸ L'.sum L).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L'.sum L) M _ n (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L →ᴸ L'.sum L).map_onFunction f x
/-
**FirstOrder.Language.LHom.sumInl_injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：sumInl_injective : (LHom.sumInl : L ->ᴸ L.sum L').Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
theorem sumInl_injective : (LHom.sumInl : L →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩
/-
**FirstOrder.Language.LHom.sumInr_injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：sumInr_injective : (LHom.sumInr : L' ->ᴸ L.sum L').Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem sumInr_injective : (LHom.sumInr : L' →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩
/-
**FirstOrder.Language.LHom.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.LHom`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isExpansionOn_reduct (ϕ : L →ᴸ L') (M : Type*) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩
/-
**FirstOrder.Language.LHom.Injective.isExpansionOn_default** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.LHom.Injective`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} {ϕ : L →ᴸ L'}   [in
st : (n : ℕ) → (f : L'.Functions n) → Decidable (f ∈ Set.range fun f => ϕ.onFunc
tion f)]   [inst_1 : (n : ℕ) → (r : L'.Relations n) → Decidable (r ∈ Set.range f
un r => ϕ.onRelation r)],   ϕ.Injective → ∀ (M : Type u_1) [inst_2 : Inhabited M
] [inst_3 : L.Structure M], ϕ.IsExpansionOn M
参数：n : ℕ；f : L'.Functions n；f ∈ Set.range fun f => ϕ.onFunction f；n : ℕ；r : L'.R
elations n；r ∈ Set.range fun r => ϕ.onRelation r；M : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.LHom.Injective.onFunction`：∀ {L : FirstOrder.Languag
e} {L' : FirstOrder.Language} {ϕ : L →ᴸ L'},   ϕ.Injective → ∀ {n : ℕ}, Function
.Injective fun f => ϕ.onFunction f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `FirstOrder.Language.LHom.Injective.onRelation`：∀ {L : FirstOrder.Languag
e} {L' : FirstOrder.Language} {ϕ : L →ᴸ L'},   ϕ.Injective → ∀ {n : ℕ}, Function
.Injective fun R => ϕ.onRelation R
-/
theorem Injective.isExpansionOn_default {ϕ : L →ᴸ L'}
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => ϕ.onFunction f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => ϕ.onRelation r)]
    (h : ϕ.Injective) (M : Type*) [Inhabited M] [L.Structure M] :
    @IsExpansionOn L L' ϕ M _ (ϕ.defaultExpansion M) := by
  let := ϕ.defaultExpansion M
  refine ⟨fun {n} f xs => ?_, fun {n} r xs => ?_⟩
  · have hf : ϕ.onFunction f ∈ Set.range fun f : L.Functions n => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r ∈ Set.range fun r : L.Relations n => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

end LHom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
/-
**FirstOrder.Language.LEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language → FirstOrder.Language → Type (max (max (max u_1 u_2) u
_3) u_4)
参数：max (max (max u_1 u_2) u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language equivalence maps the symbols of one language to symbols of another bi
jectively.
-/
structure LEquiv (L L' : Language) where
  /-- The forward language homomorphism -/
  toLHom : L →ᴸ L'
  /-- The inverse language homomorphism -/
  invLHom : L' →ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'

@[inherit_doc] infixl:10 " ≃ᴸ " => LEquiv

-- \^L
namespace LEquiv

variable (L) in
/-- The identity equivalence from a first-order language to itself. -/
@[simps]
/-
**FirstOrder.Language.LEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LEquiv`。
形式化陈述：(L : FirstOrder.Language) → L ≃ᴸ L
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity equivalence from a first-order language to itself.
-/
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩
/-
**FirstOrder.Language.LEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.LEq
uiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
/-
**FirstOrder.Language.LEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LEquiv`。
形式化陈述：{L : FirstOrder.Language} → {L' : FirstOrder.Language} → (L ≃ᴸ L') → (L' ≃
ᴸ L)
参数：L ≃ᴸ L'；L' ≃ᴸ L。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LEquiv.right_inv`：∀ {L : FirstOrder.Language} {L' : 
FirstOrder.Language} (self : L ≃ᴸ L'),   self.toLHom.comp self.invLHom = FirstOr
der.Language.LHom.id L'
· 使用定理 `FirstOrder.Language.LEquiv.left_inv`：∀ {L : FirstOrder.Language} {L' : F
irstOrder.Language} (self : L ≃ᴸ L'),   self.invLHom.comp self.toLHom = FirstOrd
er.Language.LHom.id L

--- 原说明 ---
The inverse of an equivalence of first-order languages.
-/
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
/-
**FirstOrder.Language.LEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.LEquiv`。
形式化陈述：{L : FirstOrder.Language} →   {L' : FirstOrder.Language} → {L'' : FirstOrd
er.Language} → (L ≃ᴸ L') → (L' ≃ᴸ L'') → (L ≃ᴸ L'')
参数：L ≃ᴸ L'；L' ≃ᴸ L''；L ≃ᴸ L''。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of equivalences of first-order languages.
-/
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e'.invLHom, e'.left_inv, LHom.id_comp, e.left_inv], by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e.toLHom, e.right_inv, LHom.id_comp, e'.right_inv]⟩

end LEquiv

section ConstantsOn

variable (α : Type u')

/-- The type of functions for a language consisting only of constant symbols. -/
@[simp]
/-
**FirstOrder.Language.constantsOnFunc** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage`。
形式化陈述：Type u' → ℕ → Type u'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of functions for a language consisting only of constant symbols.
-/
def constantsOnFunc : ℕ → Type u'
  | 0 => α
  | (_ + 1) => PEmpty

/-- A language with constants indexed by a type. -/
@[simps]
/-
**FirstOrder.Language.constantsOn** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
`。
形式化陈述：constantsOn : Language.{u', 0}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language with constants indexed by a type.
-/
def constantsOn : Language.{u', 0} := ⟨constantsOnFunc α, fun _ => Empty⟩
deriving IsAlgebraic

variable {α}
/-
**FirstOrder.Language.constantsOn_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language`。
形式化陈述：constantsOn_constants : (constantsOn α).Constants = α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantsOn_constants : (constantsOn α).Constants = α :=
  rfl
/-
**FirstOrder.Language.isEmpty_functions_constantsOn_succ** 是 Mathlib 中的一个实例，位于命名
空间 `FirstOrder.Language`。
形式化陈述：isEmpty_functions_constantsOn_succ {n : Nat} : IsEmpty ((constantsOn α).Fu
nctions (n + 1))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isEmpty_functions_constantsOn_succ {n : ℕ} : IsEmpty ((constantsOn α).Functions (n + 1)) :=
  inferInstanceAs (IsEmpty PEmpty)
/-
**FirstOrder.Language.isRelational_constantsOn** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language`。
形式化陈述：isRelational_constantsOn [_ie : IsEmpty α] : IsRelational (constantsOn α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isRelational_constantsOn [_ie : IsEmpty α] : IsRelational (constantsOn α) :=
  fun n => Nat.casesOn n _ie inferInstance
/-
**FirstOrder.Language.card_constantsOn** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：card_constantsOn : (constantsOn α).card = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.card_eq_card_functions_add_card_relations`：card_eq_c
ard_functions_add_card_relations : L.card = (Cardinal.sum fun l => Cardinal.lift
.{v} #(L.Functions l)) + Cardinal.sum fun l => Card…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.constantsOn_Functions`：∀ (α : Type u') (a : ℕ), (Fir
stOrder.Language.constantsOn α).Functions a = FirstOrder.Language.constantsOnFun
c α a
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.sum_nat_eq_add_sum_succ`：sum_nat_eq_add_sum_succ (f : Nat -> Ca
rdinal.{u}) : Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1)
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `FirstOrder.Language.constantsOn_Relations`：∀ (α : Type u') (x : ℕ), (Fir
stOrder.Language.constantsOn α).Relations x = Empty
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_constantsOn : (constantsOn α).card = #α := by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]

/-- Gives a `constantsOn α` structure to a type by assigning each constant a value. -/
@[instance_reducible]
/-
**FirstOrder.Language.constantsOn.structure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.constantsOn`。
形式化陈述：{M : Type w} → {α : Type u'} → (α → M) → (FirstOrder.Language.constantsOn 
α).Structure M
参数：α → M；FirstOrder.Language.constantsOn α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic

--- 原说明 ---
Gives a `constantsOn α` structure to a type by assigning each constant a value.
-/
def constantsOn.structure (f : α → M) : (constantsOn α).Structure M where
  funMap := fun {n} c _ =>
    match n, c with
    | 0, c => f c

variable {β : Type v'}

/-- A map between index types induces a map between constant languages. -/
/-
**FirstOrder.Language.LHom.constantsOnMap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.LHom`。
形式化陈述：{α : Type u'} → {β : Type v'} → (α → β) → (FirstOrder.Language.constantsOn
 α →ᴸ FirstOrder.Language.constantsOn β)
参数：α → β；FirstOrder.Language.constantsOn α →ᴸ FirstOrder.Language.constantsOn β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic

--- 原说明 ---
A map between index types induces a map between constant languages.
-/
def LHom.constantsOnMap (f : α → β) : constantsOn α →ᴸ constantsOn β where
  onFunction := fun {n} c =>
    match n, c with
    | 0, c => f c
/-
**FirstOrder.Language.constantsOnMap_isExpansionOn** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language`。
形式化陈述：constantsOnMap_isExpansionOn {f : α -> β} {fα : α -> M} {fβ : β -> M} (h :
 fβ ∘ f = fα) : @LHom.IsExpansionOn _ _ (LHom.constantsOnMap f) M (constantsOn.s
tructure fα) (constantsOn.structure fβ)
参数：h : fβ ∘ f = fα。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
-/
theorem constantsOnMap_isExpansionOn {f : α → β} {fα : α → M} {fβ : β → M} (h : fβ ∘ f = fα) :
    @LHom.IsExpansionOn _ _ (LHom.constantsOnMap f) M (constantsOn.structure fα)
      (constantsOn.structure fβ) := by
  let := constantsOn.structure fα
  let := constantsOn.structure fβ
  exact
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F :)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w')

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
/-
**FirstOrder.Language.withConstants** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：withConstants : Language.{max u w', v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extends a language with a constant for each element of a parameter set in `M`.
-/
def withConstants : Language.{max u w', v} :=
  L.sum (constantsOn α)

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:max L "[[" α "]]" => Language.withConstants L α

@[simp]
/-
**FirstOrder.Language.card_withConstants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：card_withConstants : L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.li
ft.{max u v} #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.withConstants.eq_1`：∀ (L : FirstOrder.Language) (α :
 Type w'), L.withConstants α = L.sum (FirstOrder.Language.constantsOn α)
· 使用定理 `FirstOrder.Language.card_sum`：card_sum : (L.sum L').card = Cardinal.lift
.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card
· 使用定理 `FirstOrder.Language.card_constantsOn`：card_constantsOn : (constantsOn α)
.card = #α
-/
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #α := by
  rw [withConstants, card_sum, card_constantsOn]

/-- The language map adding constants. -/
@[simps!]
/-
**FirstOrder.Language.lhomWithConstants** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：lhomWithConstants : L ->ᴸ L[[α]]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The language map adding constants.
-/
def lhomWithConstants : L →ᴸ L[[α]] :=
  LHom.sumInl
/-
**FirstOrder.Language.lhomWithConstants_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language`。
形式化陈述：lhomWithConstants_injective : (L.lhomWithConstants α).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.sumInl_injective`：sumInl_injective : (LHom.sumI
nl : L ->ᴸ L.sum L').Injective
-/
theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective

variable {α}

/-- The constant symbol indexed by a particular element. -/
/-
**FirstOrder.Language.con** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：(L : FirstOrder.Language) → {α : Type w'} → α → (L.withConstants α).Consta
nts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant symbol indexed by a particular element.
-/
protected def con (a : α) : L[[α]].Constants :=
  Sum.inr a

variable {L} (α)

/-- Adds constants to a language map. -/
/-
**FirstOrder.Language.LHom.addConstants** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.LHom`。
形式化陈述：{L : FirstOrder.Language} →   (α : Type w') → {L' : FirstOrder.Language} →
 (L →ᴸ L') → (L.withConstants α →ᴸ L'.withConstants α)
参数：α : Type w'；L →ᴸ L'；L.withConstants α →ᴸ L'.withConstants α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds constants to a language map.
-/
def LHom.addConstants {L' : Language} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sumMap (LHom.id _)
/-
**FirstOrder.Language.paramsStructure** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage`。
形式化陈述：paramsStructure (A : Set α) : (constantsOn A).Structure α
参数：A : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure (↑)

variable (L)

set_option backward.isDefEq.respectTransparency false in
/-- The language map removing an empty constant set. -/
@[simps]
/-
**FirstOrder.Language.LEquiv.addEmptyConstants** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.LEquiv`。
形式化陈述：(L : FirstOrder.Language) → (α : Type w') → [ie : IsEmpty α] → L ≃ᴸ L.with
Constants α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic

--- 原说明 ---
The language map removing an empty constant set.
-/
def LEquiv.addEmptyConstants [ie : IsEmpty α] : L ≃ᴸ L[[α]] where
  toLHom := lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr

variable {α} {β : Type*}

@[simp]
/-
**FirstOrder.Language.withConstants_funMap_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language`。
形式化陈述：withConstants_funMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).
IsExpansionOn M] {n} {f : L.Functions n} {x : Fin n -> M} : @funMap L[[α]] M _ n
 (Sum.inl f) x = funMap f x
参数：lhomWithConstants L α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
-/
theorem withConstants_funMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {f : L.Functions n} {x : Fin n → M} : @funMap L[[α]] M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x

@[simp]
/-
**FirstOrder.Language.withConstants_relMap_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language`。
形式化陈述：withConstants_relMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).
IsExpansionOn M] {n} {R : L.Relations n} {x : Fin n -> M} : @RelMap L[[α]] M _ n
 (Sum.inl R) x = RelMap R x
参数：lhomWithConstants L α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.map_onRelation`：map_onRelation {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (R : L.Relations n) (x : Fi
n n -> M) : RelMap (ϕ.onRelat…
-/
theorem withConstants_relMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {R : L.Relations n} {x : Fin n → M} : @RelMap L[[α]] M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x

/-- The language map extending the constant set. -/
/-
**FirstOrder.Language.lhomWithConstantsMap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language`。
形式化陈述：lhomWithConstantsMap (f : α -> β) : L[[α]] ->ᴸ L[[β]]
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The language map extending the constant set.
-/
def lhomWithConstantsMap (f : α → β) : L[[α]] →ᴸ L[[β]] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp]
/-
**FirstOrder.Language.LHom.map_constants_comp_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.LHom`。
形式化陈述：∀ (L : FirstOrder.Language) {α : Type w'} {β : Type u_1} {f : α → β},   (L
.lhomWithConstantsMap f).comp FirstOrder.Language.LHom.sumInl = L.lhomWithConsta
nts β
参数：L : FirstOrder.Language；L.lhomWithConstantsMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem LHom.map_constants_comp_sumInl {f : α → β} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants β := by ext <;> rfl

end

open FirstOrder

variable (α : Type*) [(constantsOn α).Structure M]

/-
**FirstOrder.Language.withConstantsStructure** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：withConstantsStructure : L[[α]].Structure M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance withConstantsStructure : L[[α]].Structure M :=
  inferInstanceAs <| (L.sum _).Structure M
/-
**FirstOrder.Language.constantsOnSelfStructure** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language`。
形式化陈述：constantsOnSelfStructure : (constantsOn M).Structure M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
-/
instance constantsOnSelfStructure : (constantsOn M).Structure M :=
  fast_instance% constantsOn.structure id
/-
**FirstOrder.Language.withConstantsSelfStructure** 是 Mathlib 中的一个实例，位于命名空间 `Firs
tOrder.Language`。
形式化陈述：withConstantsSelfStructure : L[[M]].Structure M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance withConstantsSelfStructure : L[[M]].Structure M := inferInstance
/-
**FirstOrder.Language.withConstants_self_expansion** 是 Mathlib 中的一个实例，位于命名空间 `Fi
rstOrder.Language`。
形式化陈述：withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
/-
**FirstOrder.Language.withConstants_expansion** 是 Mathlib 中的一个实例，位于命名空间 `FirstOr
der.Language`。
形式化陈述：withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
/-
**FirstOrder.Language.addEmptyConstants_is_expansion_on'** 是 Mathlib 中的一个实例，位于命名
空间 `FirstOrder.Language`。
形式化陈述：addEmptyConstants_is_expansion_on' : (LEquiv.addEmptyConstants L (∅ : Set 
M)).toLHom.IsExpansionOn M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addEmptyConstants_is_expansion_on' :
    (LEquiv.addEmptyConstants L (∅ : Set M)).toLHom.IsExpansionOn M :=
  L.withConstants_expansion _
/-
**FirstOrder.Language.addEmptyConstants_symm_isExpansionOn** 是 Mathlib 中的一个实例，位于
命名空间 `FirstOrder.Language`。
形式化陈述：addEmptyConstants_symm_isExpansionOn : (LEquiv.addEmptyConstants L (∅ : Se
t M)).symm.toLHom.IsExpansionOn M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn`：∀ {L : FirstOrder.Lang
uage} {L' : FirstOrder.Language} (M : Type u_1) [inst : L.Structure M] [inst_1 :
 L'.Structure M]   [inst_2 : L.IsAlgeb…
-/
instance addEmptyConstants_symm_isExpansionOn :
    (LEquiv.addEmptyConstants L (∅ : Set M)).symm.toLHom.IsExpansionOn M :=
  LHom.sumElim_isExpansionOn _ _ _
/-
**FirstOrder.Language.addConstants_expansion** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：addConstants_expansion {L' : Language} [L'.Structure M] (φ : L ->ᴸ L') [φ.
IsExpansionOn M] : (φ.addConstants α).IsExpansionOn M
参数：φ : L ->ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addConstants_expansion {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants α).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ M

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FirstOrder.Language.withConstants_funMap_sumInr** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language`。
形式化陈述：withConstants_funMap_sumInr {a : α} {x : Fin 0 -> M} : @funMap L[[α]] M _ 
0 (Sum.inr a : L[[α]].Functions 0) x = L.con a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
-/
theorem withConstants_funMap_sumInr {a : α} {x : Fin 0 → M} :
    @funMap L[[α]] M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a := by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α →ᴸ L.sum _).map_onFunction _ _

variable {α} (A : Set M)

@[simp]
/-
**FirstOrder.Language.coe_con** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language`。
形式化陈述：coe_con {a : A} : (L.con a : M) = a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_con {a : A} : (L.con a : M) = a :=
  rfl

variable {A} {B : Set M} (h : A ⊆ B)
/-
**FirstOrder.Language.constantsOnMap_inclusion_isExpansionOn** 是 Mathlib 中的一个实例，
位于命名空间 `FirstOrder.Language`。
形式化陈述：constantsOnMap_inclusion_isExpansionOn : (LHom.constantsOnMap (Set.inclusi
on h)).IsExpansionOn M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.constantsOnMap_isExpansionOn`：constantsOnMap_isExpan
sionOn {f : α -> β} {fα : α -> M} {fβ : β -> M} (h : fβ ∘ f = fα) : @LHom.IsExpa
nsionOn _ _ (LHom.constantsOnMap f) M …
-/
instance constantsOnMap_inclusion_isExpansionOn :
    (LHom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constantsOnMap_isExpansionOn rfl
/-
**FirstOrder.Language.map_constants_inclusion_isExpansionOn** 是 Mathlib 中的一个实例，位
于命名空间 `FirstOrder.Language`。
形式化陈述：map_constants_inclusion_isExpansionOn : (L.lhomWithConstantsMap (Set.inclu
sion h)).IsExpansionOn M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance map_constants_inclusion_isExpansionOn :
    (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ _

variable {L} (A) {N : Type w'} [L.Structure N] (f : M ↪[L] N)

/-- Type synonym for `N` used to equip it with an `L[[A]]`-structure where the new constants on `A`
are interpreted via the embedding `f`. -/
@[nolint unusedArguments]
/-
**FirstOrder.Language.Embedding.withConstants** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.Embedding`。
形式化陈述：{L : FirstOrder.Language} →   {M : Type w} → [inst : L.Structure M] → {N :
 Type w'} → [inst_1 : L.Structure N] → L.Embedding M N → Set M → Type w'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for `N` used to equip it with an `L[[A]]`-structure where the new c
onstants on `A`
are interpreted via the embedding `f`.
-/
def Embedding.withConstants (_f : M ↪[L] N) (_A : Set M) : Type w' := N
deriving L.Structure
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ↪[L] N) : (constantsOn A).Structure (f.withConstants A) :=
  fast_instance% constantsOn.structure fun a => f a
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : L[[A]].Structure (f.withConstants A) := inferInstance

/-- Lifts an embedding to the expanded language with constants. -/
/-
**FirstOrder.Language.Embedding.liftWithConstants** 是 Mathlib 中的一个定义，位于命名空间 `Fir
stOrder.Language.Embedding`。
形式化陈述：{L : FirstOrder.Language} →   {M : Type w} →     [inst : L.Structure M] → 
      (A : Set M) →         {N : Type w'} →           [inst_1 : L.Structure N] →
 (f : L.Embedding M N) → (L.withConstants ↑A).Embedding M (f.withConstants A)
参数：A : Set M；f : L.Embedding M N；L.withConstants ↑A；f.withConstants A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts an embedding to the expanded language with constants.
-/
def Embedding.liftWithConstants :
    M ↪[L[[A]]] f.withConstants A := by
  refine ⟨f.toEmbedding, ?_, ?_⟩
  · intro n g x
    cases g with
    | inl g => exact f.map_fun' g x
    | inr c =>
      cases n with
      | zero => rfl
      | succ n => exact isEmptyElim c
  · intro n R x
    cases R with
    | inl R => exact f.map_rel' R x
    | inr r => exact isEmptyElim r

end WithConstants

end Language

end FirstOrder


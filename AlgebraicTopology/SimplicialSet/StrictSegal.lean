/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Path

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _⦋n⦌ → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

open Opposite SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition if
its `m`-simplices are uniquely determined by their spine for all `m ≤ n + 1`. -/
/-
**SSet.Truncated.StrictSegal** 是 Mathlib 中的一个结构，位于命名空间 `SSet.Truncated`。
形式化陈述：StrictSegal where /-- The inverse to `spine X m`. -/ spineToSimplex (m : N
at) (h : m <= n + 1
参数：m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n + 1`-truncated simplicial set satisfies the strict Segal condition if
its `m`-simplices are uniquely determined by their spine for all `m ≤ n + 1`.
-/
structure StrictSegal where
  /-- The inverse to `spine X m`. -/
  spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by lia) : Path X m → X _⦋m⦌ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : ℕ) (h : m ≤ n + 1) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : ℕ) (h : m ≤ n + 1) :
    spineToSimplex m ∘ spine X m = id

/-- For an `n + 1`-truncated simplicial set `X`, `IsStrictSegal X` asserts the
mere existence of an inverse to `spine X m` for all `m ≤ n + 1`. -/
/-
**SSet.Truncated.IsStrictSegal** 是 Mathlib 中的一个类，位于命名空间 `SSet.Truncated`。
形式化陈述：IsStrictSegal (X : SSet.Truncated.{u} (n + 1)) : Prop where spine_bijectiv
e (X) (m : Nat) (h : m <= n + 1
参数：X : SSet.Truncated.{u} (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `n + 1`-truncated simplicial set `X`, `IsStrictSegal X` asserts the
mere existence of an inverse to `spine X m` for all `m ≤ n + 1`.
-/
class IsStrictSegal (X : SSet.Truncated.{u} (n + 1)) : Prop where
  spine_bijective (X) (m : ℕ) (h : m ≤ n + 1 := by grind) : Function.Bijective (X.spine m)

export IsStrictSegal (spine_bijective)
/-
**SSet.Truncated.spine_injective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：spine_injective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal] {m : Na
t} {h : m <= n + 1} : Function.Injective (X.spine m)
参数：X : SSet.Truncated.{u} (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `SSet.Truncated.IsStrictSegal.spine_bijective`：∀ {n : ℕ} (X : SSet.Trunca
ted (n + 1)) [self : X.IsStrictSegal] (m : ℕ)   (h : autoParam (m ≤ n + 1) SSet.
Truncated.IsStrictSegal._auto_1), …
-/
lemma spine_injective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
    {m : ℕ} {h : m ≤ n + 1} :
    Function.Injective (X.spine m) :=
  (spine_bijective X m).injective
/-
**SSet.Truncated.spine_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：spine_surjective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal] {m : N
at} (p : X.Path m) (h : m <= n + 1
参数：X : SSet.Truncated.{u} (n + 1)；p : X.Path m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `SSet.Truncated.IsStrictSegal.spine_bijective`：∀ {n : ℕ} (X : SSet.Trunca
ted (n + 1)) [self : X.IsStrictSegal] (m : ℕ)   (h : autoParam (m ≤ n + 1) SSet.
Truncated.IsStrictSegal._auto_1), …
-/
lemma spine_surjective (X : SSet.Truncated.{u} (n + 1)) [X.IsStrictSegal]
    {m : ℕ} (p : X.Path m) (h : m ≤ n + 1 := by grind) :
    ∃ (x : X _⦋m⦌ₙ₊₁), X.spine m _ x = p :=
  (spine_bijective X m).surjective p

variable {X} in
/-
**SSet.Truncated.IsStrictSegal.ext** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated.IsS
trictSegal`。
形式化陈述：∀ {n : ℕ} {X : SSet.Truncated (n + 1)} [X.IsStrictSegal] {d : ℕ} {hd : { l
en := d + 1 }.len ≤ n + 1}   {x y : X.obj (Opposite.op { obj := { len := d + 1 }
, property := hd })},   (∀ (i : Fin (d + 1)),       (CategoryTheory.ConcreteCate
gory.hom             (X.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.m
kOfSucc i) ⋯ hd).op))           x =         (CategoryTheory.ConcreteCategory.hom
             (X.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.mkOfSucc 
i) ⋯ hd).op))           y) →     x = y
参数：n + 1；Opposite.op { obj := { len := d + 1 }, property := hd }；∀ (i : Fin (d +
 1)),       (CategoryTheory.ConcreteCategory.hom             (X.map (SimplexCate
gory.Truncated.Hom.tr (SimplexCategory.mkOfSucc i) ⋯ hd).op))           x =     
    (CategoryTheory.ConcreteCategory.hom             (X.map (SimplexCategory.Tru
ncated.Hom.tr (SimplexCategory.mkOfSucc i) ⋯ hd).op))           y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.spine_injective`：spine_injective (X : SSet.Truncated.{u} 
(n + 1)) [X.IsStrictSegal] {m : Nat} {h : m <= n + 1} : Function.Injective (X.sp
ine m)
· 使用引理 `SSet.Truncated.Path.ext'`：ext' {f g : Path X (m + 1)} (h : forall i, f.a
rrow i = g.arrow i) : f = g
-/
lemma IsStrictSegal.ext [X.IsStrictSegal] {d : ℕ} {hd} {x y : X _⦋d + 1⦌ₙ₊₁}
    (h : ∀ (i : Fin (d + 1)),
      X.map (SimplexCategory.Truncated.Hom.tr (mkOfSucc i)).op x =
        X.map (SimplexCategory.Truncated.Hom.tr (mkOfSucc i)).op y) :
    x = y :=
  X.spine_injective (by ext i; apply h)

variable {X} in
/-
**SSet.Truncated.IsStrictSegal.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated
.IsStrictSegal`。
形式化陈述：∀ {n : ℕ} {X Y : SSet.Truncated (n + 1)} [Y.IsStrictSegal] {f g : X ⟶ Y}, 
  (∀ (x : X.obj (Opposite.op { obj := { len := 1 }, property := ⋯ })),       (Ca
tegoryTheory.ConcreteCategory.hom (f.app (Opposite.op { obj := { len := 1 }, pro
perty := ⋯ }))) x =         (CategoryTheory.ConcreteCategory.hom (g.app (Opposit
e.op { obj := { len := 1 }, property := ⋯ }))) x) →     f = g
参数：n + 1；∀ (x : X.obj (Opposite.op { obj := { len := 1 }, property := ⋯ })),    
   (CategoryTheory.ConcreteCategory.hom (f.app (Opposite.op { obj := { len := 1 
}, property := ⋯ }))) x =         (CategoryTheory.ConcreteCategory.hom (g.app (O
pposite.op { obj := { len := 1 }, property := ⋯ }))) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.hom_ext`：hom_ext {n : Nat} {X Y : Truncated n} {f g : X ⟶
 Y} (w : forall n, f.app n = g.app n) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.δ_comp_σ_self`：δ_comp_σ_self {n} {i : Fin (n + 1)} : δ (
Fin.castSucc i) ≫ σ i = 𝟙 ⦋n⦌
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SSet.Truncated.IsStrictSegal.ext`：∀ {n : ℕ} {X : SSet.Truncated (n + 1)}
 [X.IsStrictSegal] {d : ℕ} {hd : { len := d + 1 }.len ≤ n + 1}   {x y : X.obj (O
pposite.op { obj := { …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsStrictSegal.hom_ext {Y : SSet.Truncated.{u} (n + 1)} [Y.IsStrictSegal]
    {f g : X ⟶ Y} (h : ∀ (x : X _⦋1⦌ₙ₊₁), f.app _ x = g.app _ x) : f = g := by
  ext ⟨⟨m, hm⟩⟩ x
  induction m using SimplexCategory.rec with | _ m
  obtain _ | m := m
  · have fac := δ_comp_σ_self (i := (0 : Fin 1))
    dsimp at fac
    simpa [← NatTrans.naturality_apply,
      ← Functor.map_comp_apply, ← op_comp,
      ← SimplexCategory.Truncated.Hom.tr_comp, fac] using
      congr_arg (Y.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ 0)).op)
        (h (X.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ 0)).op x))
  · exact IsStrictSegal.ext (fun i ↦ by simp [← NatTrans.naturality_apply, h])

namespace StrictSegal

/-- Given `IsStrictSegal X`, a choice of inverse to `spine X m` for all
`m ≤ n + 1` determines an inhabitant of `StrictSegal X`. -/
/-
**SSet.Truncated.StrictSegal.ofIsStrictSegal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Tru
ncated.StrictSegal`。
形式化陈述：ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where spineToSimplex m h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.IsStrictSegal.spine_bijective`：∀ {n : ℕ} (X : SSet.Trunca
ted (n + 1)) [self : X.IsStrictSegal] (m : ℕ)   (h : autoParam (m ≤ n + 1) SSet.
Truncated.IsStrictSegal._auto_1), …

--- 原说明 ---
Given `IsStrictSegal X`, a choice of inverse to `spine X m` for all
`m ≤ n + 1` determines an inhabitant of `StrictSegal X`.
-/
noncomputable def ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where
  spineToSimplex m h :=
    Equiv.ofBijective (X.spine m) (X.spine_bijective m h) |>.invFun
  spine_spineToSimplex m _ :=
    funext <| Equiv.ofBijective (X.spine m) _ |>.right_inv
  spineToSimplex_spine m _ :=
    funext <| Equiv.ofBijective (X.spine m) _ |>.left_inv

variable {X} (sx : StrictSegal X)

section spineToSimplex

@[simp]
/-
**SSet.Truncated.StrictSegal.spine_spineToSimplex_apply** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.Truncated.StrictSegal`。
形式化陈述：spine_spineToSimplex_apply (m : Nat) (h : m <= n + 1) (f : Path X m) : X.s
pine m h (sx.spineToSimplex m h f) = f
参数：m : Nat；h : m <= n + 1；f : Path X m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `SSet.Truncated.StrictSegal.spine_spineToSimplex`：∀ {n : ℕ} {X : SSet.Tru
ncated (n + 1)} (self : X.StrictSegal) (m : ℕ) (h : m ≤ n + 1),   X.spine m h ∘ 
self.spineToSimplex m ⋯ = id
-/
lemma spine_spineToSimplex_apply (m : ℕ) (h : m ≤ n + 1) (f : Path X m) :
    X.spine m h (sx.spineToSimplex m h f) = f :=
  congr_fun (sx.spine_spineToSimplex m h) f

@[simp]
/-
**SSet.Truncated.StrictSegal.spineToSimplex_spine_apply** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.Truncated.StrictSegal`。
形式化陈述：spineToSimplex_spine_apply (m : Nat) (h : m <= n + 1) (Δ : X _⦋m⦌ₙ₊₁) : sx
.spineToSimplex m h (X.spine m h Δ) = Δ
参数：m : Nat；h : m <= n + 1；Δ : X _⦋m⦌ₙ₊₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `SSet.Truncated.StrictSegal.spineToSimplex_spine`：∀ {n : ℕ} {X : SSet.Tru
ncated (n + 1)} (self : X.StrictSegal) (m : ℕ) (h : m ≤ n + 1),   self.spineToSi
mplex m ⋯ ∘ X.spine m h = id
-/
lemma spineToSimplex_spine_apply (m : ℕ) (h : m ≤ n + 1) (Δ : X _⦋m⦌ₙ₊₁) :
    sx.spineToSimplex m h (X.spine m h Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine m h) Δ

section autoParam

variable (m : ℕ) (h : m ≤ n + 1 := by lia)

set_option backward.privateInPublic true in
/-- The fields of `StrictSegal` define an equivalence between `X _⦋m⦌ₙ₊₁`
and `Path X m`. -/
/-
**SSet.Truncated.StrictSegal.spineEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncate
d.StrictSegal`。
形式化陈述：spineEquiv : X _⦋m⦌ₙ₊₁ ≃ Path X m where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.StrictSegal.spineToSimplex_spine_apply`：spineToSimplex_sp
ine_apply (m : Nat) (h : m <= n + 1) (Δ : X _⦋m⦌ₙ₊₁) : sx.spineToSimplex m h (X.
spine m h Δ) = Δ
· 使用引理 `SSet.Truncated.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimp
lex_apply (m : Nat) (h : m <= n + 1) (f : Path X m) : X.spine m h (sx.spineToSim
plex m h f) = f

--- 原说明 ---
The fields of `StrictSegal` define an equivalence between `X _⦋m⦌ₙ₊₁`
and `Path X m`.
-/
def spineEquiv : X _⦋m⦌ₙ₊₁ ≃ Path X m where
  toFun := X.spine m
  invFun := sx.spineToSimplex m h
  left_inv := sx.spineToSimplex_spine_apply m h
  right_inv := sx.spine_spineToSimplex_apply m h

set_option backward.privateInPublic true in
/-
**SSet.Truncated.StrictSegal.spineInjective** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Trun
cated.StrictSegal`。
形式化陈述：spineInjective : Function.Injective (sx.spineEquiv m h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem spineInjective : Function.Injective (sx.spineEquiv m h) :=
  Equiv.injective _

set_option backward.privateInPublic true in
/-- In the presence of the strict Segal condition, a path of length `m` can be
"composed" by taking the diagonal edge of the resulting `m`-simplex. -/
/-
**SSet.Truncated.StrictSegal.spineToDiagonal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Tru
ncated.StrictSegal`。
形式化陈述：spineToDiagonal : Path X m -> X _⦋1⦌ₙ₊₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the presence of the strict Segal condition, a path of length `m` can be
"composed" by taking the diagonal edge of the resulting `m`-simplex.
-/
def spineToDiagonal : Path X m → X _⦋1⦌ₙ₊₁ :=
  X.map (tr (diag m)).op ∘ sx.spineToSimplex m h

end autoParam

/-- The unique existence of an inverse to `spine X m` for all `m ≤ n + 1`
implies the mere existence of such an inverse. -/
/-
**SSet.Truncated.StrictSegal.isStrictSegal** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Trunc
ated.StrictSegal`。
形式化陈述：isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where .bijective spin
e_bijective m h
参数：sx : StrictSegal X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
The unique existence of an inverse to `spine X m` for all `m ≤ n + 1`
implies the mere existence of such an inverse.
-/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  spine_bijective m h := sx.spineEquiv m h |>.bijective

variable (m : ℕ) (h : m ≤ n + 1)

@[simp]
/-
**SSet.Truncated.StrictSegal.spineToSimplex_vertex** 是 Mathlib 中的一个定理，位于命名空间 `SS
et.Truncated.StrictSegal`。
形式化陈述：spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) : X.map (tr (Simple
xCategory.const ⦋0⦌ ⦋m⦌ i)).op (sx.spineToSimplex m h f) = f.vertex i
参数：i : Fin (m + 1)；f : Path X m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Truncated.spine_vertex`：spine_vertex (Δ : X _⦋m⦌ₙ₊₁) (i : Fin (m + 
1)) : (X.spine m hₘ Δ).vertex i = X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).o
p Δ
· 使用引理 `SSet.Truncated.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimp
lex_apply (m : Nat) (h : m <= n + 1) (f : Path X m) : X.spine m h (sx.spineToSim
plex m h f) = f
-/
theorem spineToSimplex_vertex (i : Fin (m + 1)) (f : Path X m) :
    X.map (tr (SimplexCategory.const ⦋0⦌ ⦋m⦌ i)).op (sx.spineToSimplex m h f) =
      f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex_apply]

@[simp]
/-
**SSet.Truncated.StrictSegal.spineToSimplex_arrow** 是 Mathlib 中的一个定理，位于命名空间 `SSe
t.Truncated.StrictSegal`。
形式化陈述：spineToSimplex_arrow (i : Fin m) (f : Path X m) : X.map (tr (mkOfSucc i)).
op (sx.spineToSimplex m h f) = f.arrow i
参数：i : Fin m；f : Path X m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Truncated.spine_arrow`：spine_arrow (Δ : X _⦋m⦌ₙ₊₁) (i : Fin m) : (X
.spine m hₘ Δ).arrow i = X.map (tr (mkOfSucc i)).op Δ
· 使用引理 `SSet.Truncated.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimp
lex_apply (m : Nat) (h : m <= n + 1) (f : Path X m) : X.spine m h (sx.spineToSim
plex m h f) = f
-/
theorem spineToSimplex_arrow (i : Fin m) (f : Path X m) :
    X.map (tr (mkOfSucc i)).op (sx.spineToSimplex m h f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.StrictSegal.spineToSimplex_interval** 是 Mathlib 中的一个定理，位于命名空间 `
SSet.Truncated.StrictSegal`。
形式化陈述：spineToSimplex_interval (f : Path X m) (j l : Nat) (hjl : j + l <= m) : X.
map (tr (subinterval j l hjl)).op (sx.spineToSimplex m h f) = sx.spineToSimplex 
l _ (f.interval j l hjl)
参数：f : Path X m；j l : Nat；hjl : j + l <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.StrictSegal.spineInjective`：spineInjective : Function.Inj
ective (sx.spineEquiv m h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimp
lex_apply (m : Nat) (h : m <= n + 1) (f : Path X m) : X.spine m h (sx.spineToSim
plex m h f) = f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Truncated.spine_map_subinterval`：spine_map_subinterval (j l : Nat) 
(h : j + l <= m) (Δ : X _⦋m⦌ₙ₊₁) : X.spine l (by lia) (X.map (tr (subinterval j 
l h)).op Δ) = (X.spine m h…
-/
theorem spineToSimplex_interval (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (tr (subinterval j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToSimplex l _ (f.interval j l hjl) := by
  apply sx.spineInjective l
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply]
  convert! spine_map_subinterval X m h j l hjl <| sx.spineToSimplex m h f
  exact sx.spine_spineToSimplex_apply m h f |>.symm
/-
**SSet.Truncated.StrictSegal.spineToSimplex_edge** 是 Mathlib 中的一个定理，位于命名空间 `SSet
.Truncated.StrictSegal`。
形式化陈述：spineToSimplex_edge (f : Path X m) (j l : Nat) (hjl : j + l <= m) : X.map 
(tr (intervalEdge j l hjl)).op (sx.spineToSimplex m h f) = sx.spineToDiagonal l 
(by lia) (f.interval j l hjl)
参数：f : Path X m；j l : Nat；hjl : j + l <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.Truncated.StrictSegal.spineToSimplex_interval`：spineToSimplex_inter
val (f : Path X m) (j l : Nat) (hjl : j + l <= m) : X.map (tr (subinterval j l h
jl)).op (sx.spineToSimplex m h f) = sx.s…
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `SimplexCategory.Truncated.Hom.tr_comp`：∀ {n : ℕ} {a b c : SimplexCategor
y} (f : a ⟶ b) (g : b ⟶ c)   (ha : autoParam (a.len ≤ n) SimplexCategory.Truncat
ed.Hom.tr_comp._auto_1)   (…
· 使用引理 `SimplexCategory.diag_subinterval_eq`：diag_subinterval_eq {n} (j l : Nat)
 (hjl : j + l <= n) : diag l ≫ subinterval j l hjl = intervalEdge j l hjl
-/
theorem spineToSimplex_edge (f : Path X m) (j l : ℕ) (hjl : j + l ≤ m) :
    X.map (tr (intervalEdge j l hjl)).op (sx.spineToSimplex m h f) =
      sx.spineToDiagonal l (by lia) (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, Function.comp_apply]
  rw [← spineToSimplex_interval, ← Functor.map_comp_apply, ← op_comp,
    ← tr_comp, diag_subinterval_eq]

end spineToSimplex

set_option backward.isDefEq.respectTransparency.types false in
/-- For any `σ : X ⟶ Y` between `n + 1`-truncated `StrictSegal` simplicial sets,
`spineToSimplex` commutes with `Path.map`. -/
/-
**SSet.Truncated.StrictSegal.spineToSimplex_map** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
Truncated.StrictSegal`。
形式化陈述：spineToSimplex_map {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
 (sy : StrictSegal Y) (m : Nat) (h : m <= n) (f : Path X (m + 1)) (σ : X ⟶ Y) : 
sy.spineToSimplex (m + 1) _ (f.map σ) = σ.app (op ⦋m + 1⦌ₙ₊₁) (sx.spineToSimplex
 (m + 1) _ f)
参数：n + 1；sx : StrictSegal X；sy : StrictSegal Y；m : Nat；h : m <= n；f : Path X (m 
+ 1)；σ : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.StrictSegal.spineInjective`：spineInjective : Function.Inj
ective (sx.spineEquiv m h)
· 使用引理 `SSet.Truncated.Path.ext'`：ext' {f g : Path X (m + 1)} (h : forall i, f.a
rrow i = g.arrow i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.types_comp_apply`：types_comp_apply {X Y Z : Type u} (f : 
X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SSet.Truncated.StrictSegal.spineToSimplex_arrow`：spineToSimplex_arrow (i
 : Fin m) (f : Path X m) : X.map (tr (mkOfSucc i)).op (sx.spineToSimplex m h f) 
= f.arrow i
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For any `σ : X ⟶ Y` between `n + 1`-truncated `StrictSegal` simplicial sets,
`spineToSimplex` commutes with `Path.map`.
-/
lemma spineToSimplex_map {X Y : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)
    (sy : StrictSegal Y) (m : ℕ) (h : m ≤ n) (f : Path X (m + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (m + 1) _ (f.map σ) =
      σ.app (op ⦋m + 1⦌ₙ₊₁) (sx.spineToSimplex (m + 1) _ f) := by
  apply sy.spineInjective (m + 1)
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp [-NatTrans.naturality]

section spine_δ

variable (m : ℕ) (h : m ≤ n) (f : Path X (m + 1))
variable {i : Fin (m + 1)} {j : Fin (m + 2)}

set_option backward.defeqAttrib.useBackward true in
/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
/-
**SSet.Truncated.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.St
rictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particula
r,
a vertex `i` with `i < j` can be identified with the same vertex in `f`.
-/
lemma spine_δ_vertex_lt (hij : i.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.castSucc := by
  rw [spine_vertex, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    SimplexCategory.const_comp, spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_castSucc_lt j i hij]

set_option backward.defeqAttrib.useBackward true in
/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original
path. -/
/-
**SSet.Truncated.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.St
rictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original
path.
-/
lemma spine_δ_vertex_ge (hij : j ≤ i.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).vertex i = f.vertex i.succ := by
  rw [spine_vertex, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    SimplexCategory.const_comp, spineToSimplex_vertex]
  dsimp only [SimplexCategory.δ, len_mk, mkHom, Hom.toOrderHom_mk,
    Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  rw [Fin.succAbove_of_le_castSucc j i hij]

variable {i : Fin m} {j : Fin (m + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
/-
**SSet.Truncated.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.St
rictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`.
-/
lemma spine_δ_arrow_lt (hij : i.succ.castSucc < j) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.castSucc := by
  rw [spine_arrow, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_lt hij, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
/-
**SSet.Truncated.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.St
rictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path.
-/
lemma spine_δ_arrow_gt (hij : j < i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i = f.arrow i.succ := by
  rw [spine_arrow, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_gt hij, spineToSimplex_arrow]

end spine_δ

variable {X : SSet.Truncated.{u} (n + 2)} (sx : StrictSegal X) (m : ℕ)
  (h : m ≤ n + 1) (f : Path X (m + 1)) {i : Fin m} {j : Fin (m + 2)}

/-
**SSet.Truncated.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.St
rictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spine_δ_arrow_eq (hij : j = i.succ.castSucc) :
    (X.spine m _ (X.map (tr (δ j)).op
      (sx.spineToSimplex (m + 1) _ f))).arrow i =
      sx.spineToDiagonal 2 (by lia) (f.interval i 2 (by lia)) := by
  rw [spine_arrow, ← Functor.map_comp_apply, ← op_comp, ← tr_comp,
    mkOfSucc_δ_eq hij, spineToSimplex_edge]

end StrictSegal
end Truncated

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine. -/
/-
**SSet.StrictSegal** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine.
-/
structure StrictSegal where
  /-- The inverse to `spine X n`. -/
  spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌
  /-- `spineToSimplex` is a right inverse to `spine X n`. -/
  spine_spineToSimplex (n : ℕ) : spine X n ∘ spineToSimplex = id
  /-- `spineToSimplex` is a left inverse to `spine X n`. -/
  spineToSimplex_spine (n : ℕ) : spineToSimplex ∘ spine X n = id

/-- For `X` a simplicial set, `IsStrictSegal X` asserts the mere existence of
an inverse to `spine X n` for all `n : ℕ`. -/
/-
**SSet.IsStrictSegal** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `X` a simplicial set, `IsStrictSegal X` asserts the mere existence of
an inverse to `spine X n` for all `n : ℕ`.
-/
class IsStrictSegal : Prop where
  segal (n : ℕ) : Function.Bijective (spine X n)

namespace StrictSegal

/-- Given `IsStrictSegal X`, a choice of inverse to `spine X n` for all `n : ℕ`
determines an inhabitant of `StrictSegal X`. -/
/-
**SSet.StrictSegal.ofIsStrictSegal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictSegal`。
形式化陈述：ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where spineToSimplex {n}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.IsStrictSegal.segal`：∀ {X : _root_.SSet} [self : X.IsStrictSegal] (
n : ℕ), Function.Bijective (X.spine n)

--- 原说明 ---
Given `IsStrictSegal X`, a choice of inverse to `spine X n` for all `n : ℕ`
determines an inhabitant of `StrictSegal X`.
-/
noncomputable def ofIsStrictSegal [IsStrictSegal X] : StrictSegal X where
  spineToSimplex {n} :=
    Equiv.ofBijective (X.spine n) (IsStrictSegal.segal n) |>.invFun
  spine_spineToSimplex n :=
    funext <| Equiv.ofBijective (X.spine n) _ |>.right_inv
  spineToSimplex_spine n :=
    funext <| Equiv.ofBijective (X.spine n) _ |>.left_inv

variable {X} (sx : StrictSegal X)

/-- A `StrictSegal` structure on a simplicial set `X` restricts to a
`Truncated.StrictSegal` structure on the `n + 1`-truncation of `X`. -/
/-
**SSet.StrictSegal.truncation** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictSegal`。
形式化陈述：{X : _root_.SSet} → X.StrictSegal → (n : ℕ) → ((SSet.truncation (n + 1)).o
bj X).StrictSegal
参数：n : ℕ；(SSet.truncation (n + 1)).obj X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.StrictSegal.spine_spineToSimplex`：∀ {X : _root_.SSet} (self : X.Str
ictSegal) (n : ℕ), X.spine n ∘ self.spineToSimplex = id
· 使用定理 `SSet.StrictSegal.spineToSimplex_spine`：∀ {X : _root_.SSet} (self : X.Str
ictSegal) (n : ℕ), self.spineToSimplex ∘ X.spine n = id

--- 原说明 ---
A `StrictSegal` structure on a simplicial set `X` restricts to a
`Truncated.StrictSegal` structure on the `n + 1`-truncation of `X`.
-/
protected def truncation (n : ℕ) : truncation (n + 1) |>.obj X |>.StrictSegal where
  spineToSimplex _ _ := sx.spineToSimplex
  spine_spineToSimplex m _ := sx.spine_spineToSimplex m
  spineToSimplex_spine m _ := sx.spineToSimplex_spine m
/-
**SSet.StrictSegal.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.StrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.IsStrictSegal] (n : ℕ) :
    ((truncation (n + 1)).obj X).IsStrictSegal :=
  ((ofIsStrictSegal X).truncation n).isStrictSegal

@[simp]
/-
**SSet.StrictSegal.spine_spineToSimplex_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.St
rictSegal`。
形式化陈述：spine_spineToSimplex_apply {n : Nat} (f : Path X n) : X.spine n (sx.spineT
oSimplex f) = f
参数：f : Path X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `SSet.StrictSegal.spine_spineToSimplex`：∀ {X : _root_.SSet} (self : X.Str
ictSegal) (n : ℕ), X.spine n ∘ self.spineToSimplex = id
-/
lemma spine_spineToSimplex_apply {n : ℕ} (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f :=
  congr_fun (sx.spine_spineToSimplex n) f

@[simp]
/-
**SSet.StrictSegal.spineToSimplex_spine_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.St
rictSegal`。
形式化陈述：spineToSimplex_spine_apply {n : Nat} (Δ : X _⦋n⦌) : sx.spineToSimplex (X.s
pine n Δ) = Δ
参数：Δ : X _⦋n⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `SSet.StrictSegal.spineToSimplex_spine`：∀ {X : _root_.SSet} (self : X.Str
ictSegal) (n : ℕ), self.spineToSimplex ∘ X.spine n = id
-/
lemma spineToSimplex_spine_apply {n : ℕ} (Δ : X _⦋n⦌) :
    sx.spineToSimplex (X.spine n Δ) = Δ :=
  congr_fun (sx.spineToSimplex_spine n) Δ

/-- The fields of `StrictSegal` define an equivalence between `X _⦋n⦌`
and `Path X n`. -/
/-
**SSet.StrictSegal.spineEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictSegal`。
形式化陈述：spineEquiv (n : Nat) : X _⦋n⦌ ≃ Path X n where toFun
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.StrictSegal.spineToSimplex_spine_apply`：spineToSimplex_spine_apply 
{n : Nat} (Δ : X _⦋n⦌) : sx.spineToSimplex (X.spine n Δ) = Δ
· 使用引理 `SSet.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimplex_apply 
{n : Nat} (f : Path X n) : X.spine n (sx.spineToSimplex f) = f

--- 原说明 ---
The fields of `StrictSegal` define an equivalence between `X _⦋n⦌`
and `Path X n`.
-/
def spineEquiv (n : ℕ) : X _⦋n⦌ ≃ Path X n where
  toFun := X.spine n
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

variable {n : ℕ}
/-
**SSet.StrictSegal.spineInjective** 是 Mathlib 中的一个定理，位于命名空间 `SSet.StrictSegal`。
形式化陈述：spineInjective : Function.Injective (sx.spineEquiv n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem spineInjective : Function.Injective (sx.spineEquiv n) :=
  Equiv.injective _

/-- The unique existence of an inverse to `spine X n` forall `n : ℕ` implies
the mere existence of such an inverse. -/
/-
**SSet.StrictSegal.isStrictSegal** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegal`。
形式化陈述：isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where .bijective sega
l n
参数：sx : StrictSegal X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
The unique existence of an inverse to `spine X n` forall `n : ℕ` implies
the mere existence of such an inverse.
-/
lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X where
  segal n := sx.spineEquiv n |>.bijective

@[simp]
/-
**SSet.StrictSegal.spineToSimplex_vertex** 是 Mathlib 中的一个定理，位于命名空间 `SSet.StrictS
egal`。
形式化陈述：spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) : X.map (SimplexCat
egory.const ⦋0⦌ ⦋n⦌ i).op (sx.spineToSimplex f) = f.vertex i
参数：i : Fin (n + 1)；f : Path X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.spine_vertex`：spine_vertex (Δ : X _⦋n⦌) (i : Fin (n + 1)) : (X.spin
e n Δ).vertex i = X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op Δ
· 使用引理 `SSet.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimplex_apply 
{n : Nat} (f : Path X n) : X.spine n (sx.spineToSimplex f) = f
-/
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (sx.spineToSimplex f) =
      f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex_apply]

@[simp]
/-
**SSet.StrictSegal.spineToSimplex_arrow** 是 Mathlib 中的一个定理，位于命名空间 `SSet.StrictSe
gal`。
形式化陈述：spineToSimplex_arrow (i : Fin n) (f : Path X n) : X.map (mkOfSucc i).op (s
x.spineToSimplex f) = f.arrow i
参数：i : Fin n；f : Path X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.spine_arrow`：spine_arrow (Δ : X _⦋n⦌) (i : Fin n) : (X.spine n Δ).a
rrow i = X.map (mkOfSucc i).op Δ
· 使用引理 `SSet.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimplex_apply 
{n : Nat} (f : Path X n) : X.spine n (sx.spineToSimplex f) = f
-/
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex_apply]

/-- In the presence of the strict Segal condition, a path of length `n` can be
"composed" by taking the diagonal edge of the resulting `n`-simplex. -/
/-
**SSet.StrictSegal.spineToDiagonal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictSegal`。
形式化陈述：spineToDiagonal (f : Path X n) : X _⦋1⦌
参数：f : Path X n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the presence of the strict Segal condition, a path of length `n` can be
"composed" by taking the diagonal edge of the resulting `n`-simplex.
-/
def spineToDiagonal (f : Path X n) : X _⦋1⦌ :=
  SimplicialObject.diagonal X (sx.spineToSimplex f)

section interval

variable (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.StrictSegal.spineToSimplex_interval** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Stric
tSegal`。
形式化陈述：spineToSimplex_interval : X.map (subinterval j l hjl).op (sx.spineToSimple
x f) = sx.spineToSimplex (f.interval j l hjl)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.StrictSegal.spineInjective`：spineInjective : Function.Injective (sx
.spineEquiv n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.StrictSegal.spine_spineToSimplex_apply`：spine_spineToSimplex_apply 
{n : Nat} (f : Path X n) : X.spine n (sx.spineToSimplex f) = f
· 使用引理 `SSet.spine_map_subinterval`：spine_map_subinterval (j l : Nat) (h : j + l
 <= n) (Δ : X _⦋n⦌) : X.spine l (X.map (subinterval j l h).op Δ) = (X.spine n Δ)
.interval j l h
-/
theorem spineToSimplex_interval :
    X.map (subinterval j l hjl).op (sx.spineToSimplex f) =
      sx.spineToSimplex (f.interval j l hjl) := by
  apply sx.spineInjective
  dsimp only [spineEquiv, Equiv.coe_fn_mk]
  rw [spine_spineToSimplex_apply, spine_map_subinterval,
    spine_spineToSimplex_apply]
/-
**SSet.StrictSegal.spineToSimplex_edge** 是 Mathlib 中的一个定理，位于命名空间 `SSet.StrictSeg
al`。
形式化陈述：spineToSimplex_edge : X.map (intervalEdge j l hjl).op (sx.spineToSimplex f
) = sx.spineToDiagonal (f.interval j l hjl)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SSet.StrictSegal.spineToSimplex_interval`：spineToSimplex_interval : X.ma
p (subinterval j l hjl).op (sx.spineToSimplex f) = sx.spineToSimplex (f.interval
 j l hjl)
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用引理 `SimplexCategory.diag_subinterval_eq`：diag_subinterval_eq {n} (j l : Nat)
 (hjl : j + l <= n) : diag l ≫ subinterval j l hjl = intervalEdge j l hjl
-/
theorem spineToSimplex_edge :
    X.map (intervalEdge j l hjl).op (sx.spineToSimplex f) =
      sx.spineToDiagonal (f.interval j l hjl) := by
  dsimp only [spineToDiagonal, SimplicialObject.diagonal]
  rw [← spineToSimplex_interval, ← Functor.map_comp_apply, ← op_comp,
    diag_subinterval_eq]

end interval

set_option backward.isDefEq.respectTransparency.types false in
/-- For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex`
commutes with `Path.map`. -/
/-
**SSet.StrictSegal.spineToSimplex_map** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSega
l`。
形式化陈述：spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X) (sy : StrictSegal
 Y) {n : Nat} (f : Path X (n + 1)) (σ : X ⟶ Y) : sy.spineToSimplex (f.map σ) = σ
.app _ (sx.spineToSimplex f)
参数：sx : StrictSegal X；sy : StrictSegal Y；f : Path X (n + 1)；σ : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.StrictSegal.spineInjective`：spineInjective : Function.Injective (sx
.spineEquiv n)
· 使用引理 `SSet.Path.ext'`：ext' {f g : Path X (n + 1)} (h : forall i, f.arrow i = g
.arrow i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.types_comp_apply`：types_comp_apply {X Y Z : Type u} (f : 
X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `SSet.StrictSegal.spineToSimplex_arrow`：spineToSimplex_arrow (i : Fin n) 
(f : Path X n) : X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i
· 使用引理 `SSet.Path.map_arrow`：map_arrow (f : Path X n) (σ : X ⟶ Y) (i : Fin n) : 
(f.map σ).arrow i = σ.app (op ⦋1⦌) (f.arrow i)

--- 原说明 ---
For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex`
commutes with `Path.map`.
-/
lemma spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X)
    (sy : StrictSegal Y) {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    sy.spineToSimplex (f.map σ) = σ.app _ (sx.spineToSimplex f) := by
  apply sy.spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality, types_comp_apply,
    spineToSimplex_arrow, spineToSimplex_arrow, Path.map_arrow]

variable (f : Path X (n + 1))
variable {i : Fin (n + 1)} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
/-
**SSet.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particula
r,
a vertex `i` with `i < j` can be identified with the same vertex in `f`.
-/
lemma spine_δ_vertex_lt (h : i.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i =
      f.vertex i.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i h]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
/-
**SSet.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path.
-/
lemma spine_δ_vertex_ge (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc j i h]

variable {i : Fin n} {j : Fin (n + 2)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
/-
**SSet.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`.
-/
lemma spine_δ_arrow_lt (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h, spineToSimplex_arrow]

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
/-
**SSet.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path.
-/
lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h, spineToSimplex_arrow]

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
/-
**SSet.StrictSegal.spine_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`.
-/
lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i =
      sx.spineToDiagonal (f.interval i 2 (by lia)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← Functor.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h, spineToSimplex_edge]

end StrictSegal

/-- Helper structure in order to show that a simplicial set is strict Segal. -/
/-
**SSet.StrictSegalCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → ℕ → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper structure in order to show that a simplicial set is strict Segal.
-/
structure StrictSegalCore (n : ℕ) where
  /-- Map which produces an `n + 1`-simplex from a `1`-simplex and an `n`-simplex when
  the target vertex of the `1`-simplex equals the zeroth simplex of the `n`-simplex. -/
  concat (x : X _⦋1⦌) (s : X _⦋n⦌) (h : X.δ 0 x = X.map (SimplexCategory.const _ _ 0).op s) :
    X _⦋n + 1⦌
  map_mkOfSucc_zero_concat x s h : X.map (mkOfSucc 0).op (concat x s h) = x
  δ₀_concat x s h : X.δ 0 (concat x s h) = s
  injective {x y : X _⦋n + 1⦌} (h : X.map (mkOfSucc 0).op x = X.map (mkOfSucc 0).op y)
    (h₀ : X.δ 0 x = X.δ 0 y) : x = y

namespace StrictSegalCore

variable {X} (h : ∀ n, X.StrictSegalCore n) {n : ℕ} (p : X.Path n)

/-- Auxiliary definition for `StrictSegalCore.spineToSimplex`. -/
/-
**SSet.StrictSegalCore.spineToSimplexAux** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictS
egalCore`。
形式化陈述：spineToSimplexAux : { s : X _⦋n⦌ // X.spine _ s = p }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `StrictSegalCore.spineToSimplex`.
-/
def spineToSimplexAux : { s : X _⦋n⦌ // X.spine _ s = p } := by
  induction n with
  | zero => exact ⟨p.vertex 0, by aesop⟩
  | succ n hn =>
    refine ⟨(h n).concat (p.arrow 0) (hn (p.interval 1 n)).val ?_, ?_⟩
    · rw [p.arrow_tgt 0]
      exact Path.congr_vertex (hn (p.interval 1 n)).prop.symm 0
    · ext i
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · dsimp
        rw [map_mkOfSucc_zero_concat]
      · simpa [spine_arrow, ← SimplexCategory.mkOfSucc_δ_gt (j := 0) (i := i) (by simp),
          op_comp, Functor.map_comp_apply, ← SimplicialObject.δ_def, δ₀_concat,
          ← p.arrow_interval 1 n i i.succ (by grind) (by grind)] using
            Path.congr_arrow (hn (p.interval 1 n)).prop i

/-- Auxiliary definition for `StrictSegal.ofCore`. -/
/-
**SSet.StrictSegalCore.spineToSimplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictSega
lCore`。
形式化陈述：spineToSimplex : X _⦋n⦌
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `StrictSegal.ofCore`.
-/
def spineToSimplex : X _⦋n⦌ := (spineToSimplexAux h p).val

@[simp]
/-
**SSet.StrictSegalCore.spine_spineToSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Stri
ctSegalCore`。
形式化陈述：spine_spineToSimplex : X.spine n (spineToSimplex h p) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma spine_spineToSimplex : X.spine n (spineToSimplex h p) = p := (spineToSimplexAux h p).prop
/-
**SSet.StrictSegalCore.spineToSimplex_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Stric
tSegalCore`。
形式化陈述：spineToSimplex_zero (p : X.Path 0) : spineToSimplex h p = p.vertex 0
参数：p : X.Path 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spineToSimplex_zero (p : X.Path 0) : spineToSimplex h p = p.vertex 0 := rfl
/-
**SSet.StrictSegalCore.spineToSimplex_succ** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Stric
tSegalCore`。
形式化陈述：spineToSimplex_succ (p : X.Path (n + 1)) : spineToSimplex h p = (h n).conc
at (p.arrow 0) (spineToSimplex h (p.interval 1 n)) (by rw [p.arrow_tgt 0] exact 
Path.congr_vertex (spine_spineToSimplex h (p.interval 1 n)).symm 0)
参数：p : X.Path (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spineToSimplex_succ (p : X.Path (n + 1)) :
    spineToSimplex h p = (h n).concat (p.arrow 0) (spineToSimplex h (p.interval 1 n)) (by
      rw [p.arrow_tgt 0]
      exact Path.congr_vertex (spine_spineToSimplex h (p.interval 1 n)).symm 0) :=
  rfl
/-
**SSet.StrictSegalCore.map_mkOfSucc_zero_spineToSimplex** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.StrictSegalCore`。
形式化陈述：map_mkOfSucc_zero_spineToSimplex (p : X.Path (n + 1)) : X.map (mkOfSucc 0)
.op (spineToSimplex h p) = p.arrow 0
参数：p : X.Path (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.StrictSegalCore.spineToSimplex_succ`：spineToSimplex_succ (p : X.Pat
h (n + 1)) : spineToSimplex h p = (h n).concat (p.arrow 0) (spineToSimplex h (p.
interval 1 n)) (by rw [p.arrow…
· 使用定理 `SSet.StrictSegalCore.map_mkOfSucc_zero_concat`：∀ {X : _root_.SSet} {n : 
ℕ} (self : X.StrictSegalCore n) (x : X.obj (Opposite.op { len := 1 }))   (s : X.
obj (Opposite.op { len := n }))   (…
-/
lemma map_mkOfSucc_zero_spineToSimplex (p : X.Path (n + 1)) :
    X.map (mkOfSucc 0).op (spineToSimplex h p) = p.arrow 0 := by
  rw [spineToSimplex_succ, map_mkOfSucc_zero_concat]
/-
**SSet.StrictSegalCore.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.StrictSegalCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₀_spineToSimplex (p : X.Path (n + 1)) :
    X.δ 0 (spineToSimplex h p) = spineToSimplex h (p.interval 1 n) := by
  rw [spineToSimplex_succ, δ₀_concat]

@[simp]
/-
**SSet.StrictSegalCore.spineToSimplex_spine** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Stri
ctSegalCore`。
形式化陈述：spineToSimplex_spine (s : X _⦋n⦌) : spineToSimplex h (X.spine _ s) = s
参数：s : X _⦋n⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用引理 `SimplexCategory.const_eq_id`：const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SSet.StrictSegalCore.injective`：∀ {X : _root_.SSet} {n : ℕ} (self : X.St
rictSegalCore n) {x y : X.obj (Opposite.op { len := n + 1 })},   (CategoryTheory
.ConcreteCategory.ho…
· 使用引理 `SSet.StrictSegalCore.map_mkOfSucc_zero_spineToSimplex`：map_mkOfSucc_zero
_spineToSimplex (p : X.Path (n + 1)) : X.map (mkOfSucc 0).op (spineToSimplex h p
) = p.arrow 0
· 使用引理 `SSet.StrictSegalCore.δ₀_spineToSimplex`：δ₀_spineToSimplex (p : X.Path (n
 + 1)) : X.δ 0 (spineToSimplex h p) = spineToSimplex h (p.interval 1 n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.spine_δ₀`：spine_δ₀ {m : Nat} (x : X _⦋m + 1⦌) : X.spine m (X.δ 0 x)
 = (X.spine (m + 1) x).interval 1 m
-/
lemma spineToSimplex_spine (s : X _⦋n⦌) : spineToSimplex h (X.spine _ s) = s := by
  induction n with
  | zero => simp [spineToSimplex_zero]
  | succ n hn =>
    exact (h n).injective (map_mkOfSucc_zero_spineToSimplex _ _)
      (by rw [δ₀_spineToSimplex, ← hn (X.δ 0 s), spine_δ₀])

end StrictSegalCore

variable {X} in
/-- Given a simplicial set `X`, this constructs a `StrictSegal` structure for `X` from
`StrictSegalCore` structures for all `n : ℕ`. -/
/-
**SSet.StrictSegal.ofCore** 是 Mathlib 中的一个定义，位于命名空间 `SSet.StrictSegal`。
形式化陈述：{X : _root_.SSet} → ((n : ℕ) → X.StrictSegalCore n) → X.StrictSegal
参数：(n : ℕ) → X.StrictSegalCore n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a simplicial set `X`, this constructs a `StrictSegal` structure for `X` fr
om
`StrictSegalCore` structures for all `n : ℕ`.
-/
def StrictSegal.ofCore (h : ∀ n, X.StrictSegalCore n) : X.StrictSegal where
  spineToSimplex := StrictSegalCore.spineToSimplex h
  spine_spineToSimplex := by aesop
  spineToSimplex_spine n := by aesop

end SSet

namespace CategoryTheory.Nerve

open SSet

variable (C : Type u) [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- Simplices in the nerve of categories are uniquely determined by their spine.
Indeed, this property describes the essential image of the nerve functor. -/
/-
**CategoryTheory.Nerve.strictSegal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ner
ve`。
形式化陈述：strictSegal : StrictSegal (nerve C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simplices in the nerve of categories are uniquely determined by their spine.
Indeed, this property describes the essential image of the nerve functor.
-/
def strictSegal : StrictSegal (nerve C) :=
  StrictSegal.ofCore (fun n ↦
    { concat f s h := s.precomp (f.hom ≫ eqToHom (Functor.congr_obj h 0))
      map_mkOfSucc_zero_concat f s h :=
        ComposableArrows.ext₁ rfl (Functor.congr_obj h 0).symm (by cat_disch)
      δ₀_concat f s h := rfl
      injective {f g} h h₀ :=
        ComposableArrows.ext_succ (Functor.congr_obj h 0) h₀
          ((Arrow.mk_eq_mk_iff _ _).1
            (DFunLike.congr_arg ComposableArrows.arrowEquiv h)).2.2 })
/-
**CategoryTheory.Nerve.isStrictSegal** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.N
erve`。
形式化陈述：isStrictSegal : IsStrictSegal (nerve C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.StrictSegal.isStrictSegal`：isStrictSegal (sx : StrictSegal X) : IsS
trictSegal X where .bijective segal n
-/
instance isStrictSegal : IsStrictSegal (nerve C) :=
  strictSegal C |>.isStrictSegal

end CategoryTheory.Nerve


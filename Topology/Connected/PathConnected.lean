/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Path

/-!
# Path connectedness

Continuing from `Mathlib/Topology/Path.lean`, this file defines path components and path-connected
spaces.

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Joined (x y : X)` means there is a path between `x` and `y`.
* `Joined.somePath (h : Joined x y)` selects some path between two points `x` and `y`.
* `pathComponent (x : X)` is the set of points joined to `x`.
* `PathConnectedSpace X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : Set X`.

* `JoinedIn F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `JoinedIn.somePath (h : JoinedIn F x y)` selects a path from `x` to `y` inside `F`.
* `pathComponentIn F (x : X)` is the set of points joined to `x` in `F`.
* `IsPathConnected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.

## Main theorems

* `Joined` is an equivalence relation, while `JoinedIn F` is at least symmetric and transitive.

One can link the absolute and relative version in two directions, using `(univ : Set X)` or the
subtype `↥F`.

* `pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X)`
* `isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace ↥F`

Furthermore, it is shown that continuous images and quotients of path-connected sets/spaces are
path-connected, and that every path-connected set/space is also connected. (See
`Counterexamples.TopologistsSineCurve` for an example of a set in `ℝ × ℝ` that is connected but not
path-connected.)
-/

@[expose] public section

noncomputable section

open Topology Filter unitInterval Set Function Pointwise Fin

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Being joined by a path -/


/-- The relation "being joined by a path". This is an equivalence relation. -/
/-
**Joined** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Joined (x y : X) : Prop
参数：x y : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation "being joined by a path". This is an equivalence relation.
-/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)

@[refl]
/-
**Joined.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.refl (x : X) : Joined x x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩

/-- When two points are joined, choose some path from `x` to `y`. -/
/-
**Joined.somePath** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Joined.somePath (h : Joined x y) : Path x y
参数：h : Joined x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When two points are joined, choose some path from `x` to `y`.
-/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h

@[symm]
/-
**Joined.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.symm {x y : X} (h : Joined x y) : Joined y x
参数：h : Joined x y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩

@[trans]
/-
**Joined.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x 
z
参数：hxy : Joined x y；hyz : Joined y z。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩
/-
**Joined.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.map {x y : X} {f : X -> Y} (h : Joined x y) (hf : Continuous f) : J
oined (f x) (f y)
参数：h : Joined x y；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Joined.map {x y : X} {f : X → Y} (h : Joined x y) (hf : Continuous f) :
    Joined (f x) (f y) :=
  ⟨h.somePath.map hf⟩

@[to_additive]
/-
**Joined.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M] {a b
 c d : M} (hs : Joined a b) (ht : Joined c d) : Joined (a * c) (b * d)
参数：hs : Joined a b；ht : Joined c d。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Joined.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {a b c d : M} (hs : Joined a b) (ht : Joined c d) : Joined (a * c) (b * d) :=
  ⟨hs.somePath.mul ht.somePath⟩

@[to_additive]
/-
**Joined.listProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.listProd {M : Type*} [MulOneClass M] [TopologicalSpace M] [Continuo
usMul M] {l l' : List M} (h : List.Forall₂ Joined l l') : Joined l.prod l'.prod
参数：h : List.Forall₂ Joined l l'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Joined.refl`：Joined.refl (x : X) : Joined x x
· 使用定理 `Joined.mul`：Joined.mul {M : Type*} [Mul M] [TopologicalSpace M] [Continu
ousMul M] {a b c d : M} (hs : Joined a b) (ht : Joined c d) : Joined (a * c) (b 
…
-/
theorem Joined.listProd {M : Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M]
    {l l' : List M} (h : List.Forall₂ Joined l l') :
    Joined l.prod l'.prod := by
  induction h with
  | nil => rfl
  | cons h₁ _ h₂ => exact h₁.mul h₂

@[to_additive]
/-
**Joined.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.inv {G : Type*} [Inv G] [TopologicalSpace G] [ContinuousInv G] {x y
 : G} (h : Joined x y) : Joined x⁻¹ y⁻¹
参数：h : Joined x y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Joined.inv {G : Type*} [Inv G] [TopologicalSpace G] [ContinuousInv G]
    {x y : G} (h : Joined x y) : Joined x⁻¹ y⁻¹ :=
  ⟨h.somePath.inv⟩

variable (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
@[instance_reducible]
/-
**pathSetoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pathSetoid : Setoid X where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid corresponding the equivalence relation of being joined by a continuou
s path.
-/
def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
/-
**ZerothHomotopy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ZerothHomotopy
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient type of points of a topological space modulo being joined by a cont
inuous path.
-/
def ZerothHomotopy :=
  Quotient (pathSetoid X)

namespace ZerothHomotopy

variable {X}

/-- The map `X → ZerothHomotopy X`. -/
/-
**ZerothHomotopy.mk** 是 Mathlib 中的一个定义，位于命名空间 `ZerothHomotopy`。
形式化陈述：mk (x : X) : ZerothHomotopy X
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `X → ZerothHomotopy X`.
-/
def mk (x : X) : ZerothHomotopy X := Quotient.mk _ x
/-
**ZerothHomotopy.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `ZerothHomotopy`。
形式化陈述：mk_surjective : Function.Surjective (mk (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_surjective : Function.Surjective (mk (X := X)) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**ZerothHomotopy.rec** 是 Mathlib 中的一个引理，位于命名空间 `ZerothHomotopy`。
形式化陈述：rec {motive : ZerothHomotopy X -> Prop} (mk : forall (x : X), motive (.mk 
x)) (x : ZerothHomotopy X) : motive x
参数：mk : forall (x : X), motive (.mk x)；x : ZerothHomotopy X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZerothHomotopy.mk_surjective`：mk_surjective : Function.Surjective (mk (X
-/
lemma rec {motive : ZerothHomotopy X → Prop}
    (mk : ∀ (x : X), motive (.mk x)) (x : ZerothHomotopy X) :
    motive x := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  exact mk x
/-
**ZerothHomotopy.sound** 是 Mathlib 中的一个引理，位于命名空间 `ZerothHomotopy`。
形式化陈述：sound {x y : X} (p : Path x y) : mk x = mk y
参数：p : Path x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
lemma sound {x y : X} (p : Path x y) : mk x = mk y :=
  Quotient.sound ⟨p⟩

/-- The quotient topology on path components. -/
/-
**ZerothHomotopy.** 是 Mathlib 中的一个实例，位于命名空间 `ZerothHomotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient topology on path components.
-/
instance : TopologicalSpace <| ZerothHomotopy X :=
  inferInstanceAs <| TopologicalSpace <| Quotient _
/-
**ZerothHomotopy.isQuotientMap_mk** 是 Mathlib 中的一个引理，位于命名空间 `ZerothHomotopy`。
形式化陈述：isQuotientMap_mk : IsQuotientMap (ZerothHomotopy.mk (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
-/
lemma isQuotientMap_mk : IsQuotientMap (ZerothHomotopy.mk (X := X)) :=
  isQuotientMap_quotient_mk'
/-
**ZerothHomotopy.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `ZerothHomotopy`。
形式化陈述：inhabited : Inhabited (ZerothHomotopy Real)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
instance inhabited : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotient.mk' ℝ (pathSetoid ℝ) 0⟩
/-
**ZerothHomotopy.** 是 Mathlib 中的一个实例，位于命名空间 `ZerothHomotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty X] : Nonempty (ZerothHomotopy X) := ⟨.mk (Classical.arbitrary _)⟩

section

variable {T : Type*} (f : X → T) (hf : ∀ ⦃x y : X⦄ (_ : Path x y), f x = f y)

/-- Constructor for maps from `ZerothHomotopy X`. -/
/-
**ZerothHomotopy.lift** 是 Mathlib 中的一个定义，位于命名空间 `ZerothHomotopy`。
形式化陈述：lift : ZerothHomotopy X -> T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for maps from `ZerothHomotopy X`.
-/
def lift : ZerothHomotopy X → T :=
  Quotient.lift f fun _ _ ⟨p⟩ ↦ hf p

@[simp]
/-
**ZerothHomotopy.lift_mk** 是 Mathlib 中的一个引理，位于命名空间 `ZerothHomotopy`。
形式化陈述：lift_mk (x : X) : lift f hf (.mk x) = f x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_mk (x : X) : lift f hf (.mk x) = f x := rfl

end

end ZerothHomotopy

variable {X}

/-! ### Being joined by a path inside a set -/


/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
/-
**JoinedIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：JoinedIn (F : Set X) (x y : X) : Prop
参数：F : Set X；x y : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation "being joined by a path in `F`". Not quite an equivalence relation 
since it's not
reflexive for points that do not belong to `F`.
-/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F

variable {F : Set X}
/-
**JoinedIn.mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F
参数：h : JoinedIn F x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
-/
theorem JoinedIn.mem (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this
/-
**JoinedIn.source_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.source_mem (h : JoinedIn F x y) : x in F
参数：h : JoinedIn F x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `JoinedIn.mem`：JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F
-/
theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.mem.1
/-
**JoinedIn.target_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.target_mem (h : JoinedIn F x y) : y in F
参数：h : JoinedIn F x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `JoinedIn.mem`：JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F
-/
theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.mem.2

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
/-
**JoinedIn.somePath** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：JoinedIn.somePath (h : JoinedIn F x y) : Path x y
参数：h : JoinedIn F x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F`
-/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h

@[simp]
/-
**JoinedIn.somePath_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t in F
参数：h : JoinedIn F x y；t : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t ∈ F :=
  Classical.choose_spec h t

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
/-
**JoinedIn.joined_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.joined_subtype (h : JoinedIn F x y) : Joined (⟨x, h.source_mem⟩ :
 F) (⟨y, h.target_mem⟩ : F)
参数：h : JoinedIn F x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.source_mem`：JoinedIn.source_mem (h : JoinedIn F x y) : x in F
· 使用定理 `JoinedIn.target_mem`：JoinedIn.target_mem (h : JoinedIn F x y) : y in F
· 使用定理 `JoinedIn.somePath_mem`：JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I
) : h.somePath t in F
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y

--- 原说明 ---
If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F
`.
-/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{  toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩
/-
**JoinedIn.ofLine** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.ofLine {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁
 : f 1 = y) (hF : f '' I subseteq F) : JoinedIn F x y
参数：hf : ContinuousOn f I；h₀ : f 0 = x；h₁ : f 1 = y；hF : f '' I subseteq F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ofLine_mem`：ofLine_mem {f : Real -> X} (hf : ContinuousOn f I) (h₀ 
: f 0 = x) (h₁ : f 1 = y) : forall t, ofLine hf h₀ h₁ t in f '' I
-/
theorem JoinedIn.ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I ⊆ F) : JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF <| Path.ofLine_mem hf h₀ h₁ t⟩
/-
**JoinedIn.joined** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.joined (h : JoinedIn F x y) : Joined x y
参数：h : JoinedIn F x y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩
/-
**joinedIn_iff_joined** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：joinedIn_iff_joined (x_in : x in F) (y_in : y in F) : JoinedIn F x y ↔ Joi
ned (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F)
参数：x_in : x in F；y_in : y in F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.joined_subtype`：JoinedIn.joined_subtype (h : JoinedIn F x y) : 
Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Path.map_coe`：map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) : (
γ.map h : I -> Y) = f ∘ γ
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem joinedIn_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]
/-
**joinedIn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：joinedIn_univ : JoinedIn univ x y ↔ Joined x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]
/-
**JoinedIn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U subseteq V) : Jo
inedIn V x y
参数：h : JoinedIn U x y；hUV : U subseteq V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.somePath_mem`：JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I
) : h.somePath t in F
-/
theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩
/-
**JoinedIn.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.refl (h : x in F) : JoinedIn F x x
参数：h : x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun _t => h⟩

@[symm]
/-
**JoinedIn.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x
参数：h : JoinedIn F x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.mem`：JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F
· 使用定理 `Joined.symm`：Joined.symm {x y : X} (h : Joined x y) : Joined y x
-/
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
  obtain ⟨hx, hy⟩ := h.mem
  simp_all only [joinedIn_iff_joined]
  exact h.symm
/-
**JoinedIn.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F 
x z
参数：hxy : JoinedIn F x y；hyz : JoinedIn F y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.mem`：JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F
· 使用定理 `Joined.trans`：Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined 
y z) : Joined x z
-/
theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
  obtain ⟨hx, hy⟩ := hxy.mem
  obtain ⟨hx, hy⟩ := hyz.mem
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz
/-
**Specializes.joinedIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.joinedIn (h : x ⤳ y) (hx : x in F) (hy : y in F) : JoinedIn F 
x y
参数：h : x ⤳ y；hx : x in F；hy : y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.continuous_piecewise_of_specializes`：IsClosed.continuous_piecew
ise_of_specializes [DecidablePred (· in s)] (hs : IsClosed s) (hf : Continuous f
) (hg : Continuous g) (hspec : for…
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem Specializes.joinedIn (h : x ⤳ y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y := by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t ↦ ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ ↦ h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption
/-
**Inseparable.joinedIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.joinedIn (h : Inseparable x y) (hx : x in F) (hy : y in F) : J
oinedIn F x y
参数：h : Inseparable x y；hx : x in F；hy : y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.joinedIn`：Specializes.joinedIn (h : x ⤳ y) (hx : x in F) (hy
 : y in F) : JoinedIn F x y
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
-/
theorem Inseparable.joinedIn (h : Inseparable x y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y :=
  h.specializes.joinedIn hx hy
/-
**JoinedIn.map_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.map_continuousOn (h : JoinedIn F x y) {f : X -> Y} (hf : Continuo
usOn f F) : JoinedIn (f '' F) (f x) (f y)
参数：h : JoinedIn F x y；hf : ContinuousOn f F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem JoinedIn.map_continuousOn (h : JoinedIn F x y) {f : X → Y} (hf : ContinuousOn f F) :
    JoinedIn (f '' F) (f x) (f y) :=
  let ⟨γ, hγ⟩ := h
  ⟨γ.map' <| hf.mono (range_subset_iff.mpr hγ), fun t ↦ mem_image_of_mem _ (hγ t)⟩
/-
**JoinedIn.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.map (h : JoinedIn F x y) {f : X -> Y} (hf : Continuous f) : Joine
dIn (f '' F) (f x) (f y)
参数：h : JoinedIn F x y；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.map_continuousOn`：JoinedIn.map_continuousOn (h : JoinedIn F x y
) {f : X -> Y} (hf : ContinuousOn f F) : JoinedIn (f '' F) (f x) (f y)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem JoinedIn.map (h : JoinedIn F x y) {f : X → Y} (hf : Continuous f) :
    JoinedIn (f '' F) (f x) (f y) :=
  h.map_continuousOn hf.continuousOn
/-
**Topology.IsInducing.joinedIn_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.joinedIn_image {f : X -> Y} (hf : IsInducing f) (hx : 
x in F) (hy : y in F) : JoinedIn (f '' F) (f x) (f y) ↔ JoinedIn F x y
参数：hf : IsInducing f；hx : x in F；hy : y in F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `JoinedIn.trans`：JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F 
y z) : JoinedIn F x z
· 使用定理 `Specializes.joinedIn`：Specializes.joinedIn (h : x ⤳ y) (hx : x in F) (hy
 : y in F) : JoinedIn F x y
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `JoinedIn.map`：JoinedIn.map (h : JoinedIn F x y) {f : X -> Y} (hf : Conti
nuous f) : JoinedIn (f '' F) (f x) (f y)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
-/
theorem Topology.IsInducing.joinedIn_image {f : X → Y} (hf : IsInducing f) (hx : x ∈ F)
    (hy : y ∈ F) : JoinedIn (f '' F) (f x) (f y) ↔ JoinedIn F x y := by
  refine ⟨?_, (.map · hf.continuous)⟩
  rintro ⟨γ, hγ⟩
  choose γ' hγ'F hγ' using hγ
  have h₀ : x ⤳ γ' 0 := by rw [← hf.specializes_iff, hγ', γ.source]
  have h₁ : γ' 1 ⤳ y := by rw [← hf.specializes_iff, hγ', γ.target]
  have h : JoinedIn F (γ' 0) (γ' 1) := by
    refine ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'F⟩
    simpa only [hf.continuous_iff, comp_def, hγ'] using map_continuous γ
  exact (h₀.joinedIn hx (hγ'F _)).trans <| h.trans <| h₁.joinedIn (hγ'F _) hy

@[to_additive]
/-
**JoinedIn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M] {s
 t : Set M} {a b c d : M} (hs : JoinedIn s a b) (ht : JoinedIn t c d) : JoinedIn
 (s * t) (a * c) (b * d)
参数：hs : JoinedIn s a b；ht : JoinedIn t c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `JoinedIn.somePath_mem`：JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I
) : h.somePath t in F
-/
theorem JoinedIn.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {s t : Set M} {a b c d : M} (hs : JoinedIn s a b) (ht : JoinedIn t c d) :
    JoinedIn (s * t) (a * c) (b * d) :=
  ⟨hs.somePath.mul ht.somePath, fun t ↦ Set.mul_mem_mul (hs.somePath_mem t) (ht.somePath_mem t)⟩

@[to_additive]
/-
**JoinedIn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [Continuou
sInv G] {s : Set G} {a b : G} (hs : JoinedIn s a b) : JoinedIn s⁻¹ a⁻¹ b⁻¹
参数：hs : JoinedIn s a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inv_mem_inv`：inv_mem_inv : a⁻¹ in s⁻¹ ↔ a in s
· 使用定理 `JoinedIn.somePath_mem`：JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I
) : h.somePath t in F
-/
theorem JoinedIn.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
    {s : Set G} {a b : G} (hs : JoinedIn s a b) :
    JoinedIn s⁻¹ a⁻¹ b⁻¹ :=
  ⟨hs.somePath.inv, fun t ↦ Set.inv_mem_inv.mpr (hs.somePath_mem t)⟩

/-! ### Path component -/

/-- The path component of `x` is the set of points that can be joined to `x`. -/
/-
**pathComponent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pathComponent (x : X)
参数：x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path component of `x` is the set of points that can be joined to `x`.
-/
def pathComponent (x : X) :=
  { y | Joined x y }
/-
**mem_pathComponent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_pathComponent_iff : x in pathComponent y ↔ Joined y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pathComponent_iff : x ∈ pathComponent y ↔ Joined y x := .rfl

@[simp]
/-
**mem_pathComponent_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_pathComponent_self (x : X) : x in pathComponent x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Joined.refl`：Joined.refl (x : X) : Joined x x
-/
theorem mem_pathComponent_self (x : X) : x ∈ pathComponent x :=
  Joined.refl x

@[simp]
/-
**pathComponent.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent.nonempty (x : X) : (pathComponent x).Nonempty
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_pathComponent_self`：mem_pathComponent_self (x : X) : x in pathCompon
ent x
-/
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩
/-
**mem_pathComponent_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_pathComponent_of_mem (h : x in pathComponent y) : y in pathComponent x
参数：h : x in pathComponent y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Joined.symm`：Joined.symm {x y : X} (h : Joined x y) : Joined y x
-/
theorem mem_pathComponent_of_mem (h : x ∈ pathComponent y) : y ∈ pathComponent x :=
  Joined.symm h
/-
**pathComponent_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent_symm : x in pathComponent y ↔ y in pathComponent x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_pathComponent_of_mem`：mem_pathComponent_of_mem (h : x in pathCompone
nt y) : y in pathComponent x
-/
theorem pathComponent_symm : x ∈ pathComponent y ↔ y ∈ pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩
/-
**pathComponent_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent_congr (h : x in pathComponent y) : pathComponent x = pathCom
ponent y
参数：h : x in pathComponent y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathComponent_symm`：pathComponent_symm : x in pathComponent y ↔ y in pat
hComponent x
· 使用定理 `Joined.symm`：Joined.symm {x y : X} (h : Joined x y) : Joined y x
· 使用定理 `Joined.trans`：Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined 
y z) : Joined x z
-/
theorem pathComponent_congr (h : x ∈ pathComponent y) : pathComponent x = pathComponent y := by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h
/-
**pathComponent_subset_component** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent_subset_component (x : X) : pathComponent x subseteq connecte
dComponent x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.subset_connectedComponent`：IsConnected.subset_connectedCompo
nent {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x in s) : s subseteq connect
edComponent x
· 使用定理 `isConnected_range`：isConnected_range [TopologicalSpace β] [ConnectedSpac
e α] {f : α -> β} (h : Continuous f) : IsConnected (range f)
· 使用定理 `unitInterval.instConnectedSpaceElemReal`：ConnectedSpace ↑unitInterval
· 使用定理 `Path.continuous`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y), Continuous ⇑γ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
-/
theorem pathComponent_subset_component (x : X) : pathComponent x ⊆ connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

/-- Every connected component is a union of path connected components -/
/-
**biUnion_connectedComponent_pathComponent_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biUnion_connectedComponent_pathComponent_eq (x : X) : (⋃ y in connectedCom
ponent x, pathComponent y) = connectedComponent x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathComponent_subset_component`：pathComponent_subset_component (x : X) :
 pathComponent x subseteq connectedComponent x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `connectedComponent_eq`：connectedComponent_eq {x y : α} (h : y in connect
edComponent x) : connectedComponent x = connectedComponent y
· 使用定理 `mem_pathComponent_self`：mem_pathComponent_self (x : X) : x in pathCompon
ent x

--- 原说明 ---
Every connected component is a union of path connected components
-/
theorem biUnion_connectedComponent_pathComponent_eq (x : X) :
    (⋃ y ∈ connectedComponent x, pathComponent y) = connectedComponent x := by
  simp only [Set.ext_iff, mem_iUnion₂]
  exact fun z ↦ ⟨fun ⟨y, hy, hz⟩ ↦ connectedComponent_eq hy ▸ pathComponent_subset_component _ hz,
    (⟨z, ·, mem_pathComponent_self z⟩)⟩

/-- The canonical map which sends a path component of `X` (as a term of `ZerothHomotopy X`) to the
connected component containing it (as a term of `ConnectedComponents X`). -/
/-
**ZerothHomotopy.toConnectedComponents** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ZerothHomotopy.toConnectedComponents : ZerothHomotopy X -> ConnectedCompon
ents X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map which sends a path component of `X` (as a term of `ZerothHomot
opy X`) to the
connected component containing it (as a term of `ConnectedComponents X`).
-/
def ZerothHomotopy.toConnectedComponents : ZerothHomotopy X → ConnectedComponents X :=
  Quotient.map id fun x _ h ↦ connectedComponent_eq <| pathComponent_subset_component x h

@[simp]
/-
**ZerothHomotopy.toConnectedComponents_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZerothHomotopy.toConnectedComponents_apply (x : X) : toConnectedComponents
 (.mk x) = ⟦x⟧
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ZerothHomotopy.toConnectedComponents_apply (x : X) :
    toConnectedComponents (.mk x) = ⟦x⟧ := rfl

/-- There are at least as many path connected components as there are connected components -/
/-
**ZerothHomotopy.toConnectedComponents_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZerothHomotopy.toConnectedComponents_surjective : .Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map_surjective`：Quotient.map_surjective {sa : Setoid α} {sb : S
etoid β} {f : α -> β} .Surjective
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id

--- 原说明 ---
There are at least as many path connected components as there are connected comp
onents
-/
theorem ZerothHomotopy.toConnectedComponents_surjective :
    toConnectedComponents (X := X) |>.Surjective :=
  Quotient.map_surjective _ surjective_id

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
/-
**pathComponentIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pathComponentIn (F : Set X) (x : X)
参数：F : Set X；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path component of `x` in `F` is the set of points that can be joined to `x` 
in `F`.
-/
def pathComponentIn (F : Set X) (x : X) :=
  { y | JoinedIn F x y }

@[simp]
/-
**pathComponentIn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponentIn_univ (x : X) : pathComponentIn univ x = pathComponent x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pathComponentIn_univ (x : X) : pathComponentIn univ x = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]
/-
**Joined.mem_pathComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.mem_pathComponent (hyz : Joined y z) (hxy : y in pathComponent x) :
 z in pathComponent x
参数：hyz : Joined y z；hxy : y in pathComponent x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Joined.trans`：Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined 
y z) : Joined x z
-/
theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y ∈ pathComponent x) :
    z ∈ pathComponent x :=
  hxy.trans hyz
/-
**mem_pathComponentIn_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_pathComponentIn_self (h : x in F) : x in pathComponentIn F x
参数：h : x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.refl`：JoinedIn.refl (h : x in F) : JoinedIn F x x
-/
theorem mem_pathComponentIn_self (h : x ∈ F) : x ∈ pathComponentIn F x :=
  JoinedIn.refl h
/-
**pathComponentIn_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponentIn_subset : pathComponentIn F x subseteq F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.target_mem`：JoinedIn.target_mem (h : JoinedIn F x y) : y in F
-/
theorem pathComponentIn_subset : pathComponentIn F x ⊆ F :=
  fun _ hy ↦ hy.target_mem
/-
**pathComponentIn_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponentIn_nonempty_iff : (pathComponentIn F x).Nonempty ↔ x in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
-/
theorem pathComponentIn_nonempty_iff : (pathComponentIn F x).Nonempty ↔ x ∈ F :=
  ⟨fun ⟨_, ⟨γ, hγ⟩⟩ ↦ γ.source ▸ hγ 0, fun hx ↦ ⟨x, mem_pathComponentIn_self hx⟩⟩
/-
**pathComponentIn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponentIn_congr (h : x in pathComponentIn F y) : pathComponentIn F x
 = pathComponentIn F y
参数：h : x in pathComponentIn F y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `JoinedIn.trans`：JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F 
y z) : JoinedIn F x z
· 使用定理 `JoinedIn.symm`：JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x
-/
theorem pathComponentIn_congr (h : x ∈ pathComponentIn F y) :
    pathComponentIn F x = pathComponentIn F y := by
  ext; exact ⟨h.trans, h.symm.trans⟩

@[gcongr]
/-
**pathComponentIn_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponentIn_mono {G : Set X} (h : F subseteq G) : pathComponentIn F x 
subseteq pathComponentIn G x
参数：h : F subseteq G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pathComponentIn_mono {G : Set X} (h : F ⊆ G) :
    pathComponentIn F x ⊆ pathComponentIn G x :=
  fun _ ⟨γ, hγ⟩ ↦ ⟨γ, fun t ↦ h (hγ t)⟩

/-! ### Path component of the identity in a group -/

/-- The path component of the identity in a topological monoid, as a submonoid. -/
@[to_additive (attr := simps) /-- The path component of the identity in an additive topological
monoid, as an additive submonoid. -/]
/-
**Submonoid.pathComponentOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.pathComponentOne (M : Type*) [Monoid M] [TopologicalSpace M] [Co
ntinuousMul M] : Submonoid M where carrier
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Submonoid.pathComponentOne (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    Submonoid M where
  carrier := pathComponent (1 : M)
  mul_mem' {m₁ m₂} hm₁ hm₂ := by simpa using! hm₁.mul hm₂
  one_mem' := mem_pathComponent_self 1

/-- The path component of the identity in a topological group, as a subgroup. -/
@[to_additive (attr := simps!) /-- The path component of the identity in an additive topological
group, as an additive subgroup. -/]
/-
**Subgroup.pathComponentOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G] [IsTo
pologicalGroup G] : Subgroup G where toSubmonoid
参数：G : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
def Subgroup.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup G where
  toSubmonoid := .pathComponentOne G
  inv_mem' {g} hg := by simpa using! hg.inv

/-- The path component of the identity in a topological group is normal. -/
@[to_additive]
/-
**Subgroup.Normal.pathComponentOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.Normal.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G
] [IsTopologicalGroup G] : (Subgroup.pathComponentOne G).Normal where conj_mem _
参数：G : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y

--- 原说明 ---
The path component of the identity in a topological group is normal.
-/
instance Subgroup.Normal.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (Subgroup.pathComponentOne G).Normal where
  conj_mem _ := fun ⟨γ⟩ g ↦ ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩

/-! ### Path connected sets -/


/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
/-
**IsPathConnected** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPathConnected (F : Set X) : Prop
参数：F : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `F` is path connected if it contains a point that can be joined to all oth
er in `F`.
-/
def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ ⦃y⦄, y ∈ F → JoinedIn F x y
/-
**isPathConnected_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_iff_eq : IsPathConnected F ↔ exists x in F, pathComponentI
n F x = F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `JoinedIn.mem`：JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPathConnected_iff_eq : IsPathConnected F ↔ ∃ x ∈ F, pathComponentIn F x = F := by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, @h _⟩
  · intro y y_in
    rwa [← h] at y_in
/-
**IsPathConnected.joinedIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.joinedIn (h : IsPathConnected F) : forallᵉ (x in F) (y in 
F), JoinedIn F x y
参数：h : IsPathConnected F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.trans`：JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F 
y z) : JoinedIn F x z
· 使用定理 `JoinedIn.symm`：JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x
-/
theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y := fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)
/-
**isPathConnected_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_iff : IsPathConnected F ↔ F.Nonempty ∧ forallᵉ (x in F) (y
 in F), JoinedIn F x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y
-/
theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, h _ b_in⟩⟩
/-
**IsPathConnected.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.nonempty (h : IsPathConnected F) : F.Nonempty
参数：h : IsPathConnected F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPathConnected_iff`：isPathConnected_iff : IsPathConnected F ↔ F.Nonempt
y ∧ forallᵉ (x in F) (y in F), JoinedIn F x y
-/
theorem IsPathConnected.nonempty (h : IsPathConnected F) : F.Nonempty :=
  isPathConnected_iff.mp h |>.1

/-- If `f` is continuous on `F` and `F` is path-connected, so is `f(F)`. -/
/-
**IsPathConnected.image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.image' (hF : IsPathConnected F) {f : X -> Y} (hf : Continu
ousOn f F) : IsPathConnected (f '' F)
参数：hF : IsPathConnected F；hf : ContinuousOn f F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `JoinedIn.somePath_mem`：JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I
) : h.somePath t in F

--- 原说明 ---
If `f` is continuous on `F` and `F` is path-connected, so is `f(F)`.
-/
theorem IsPathConnected.image' (hF : IsPathConnected F)
    {f : X → Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F) := by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t ↦ ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

/-- If `f` is continuous and `F` is path-connected, so is `f(F)`. -/
/-
**IsPathConnected.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.image (hF : IsPathConnected F) {f : X -> Y} (hf : Continuo
us f) : IsPathConnected (f '' F)
参数：hF : IsPathConnected F；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.image'`：IsPathConnected.image' (hF : IsPathConnected F) 
{f : X -> Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
If `f` is continuous and `F` is path-connected, so is `f(F)`.
-/
theorem IsPathConnected.image (hF : IsPathConnected F) {f : X → Y} (hf : Continuous f) :
    IsPathConnected (f '' F) :=
  hF.image' hf.continuousOn

@[to_additive]
/-
**IsPathConnected.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMu
l M] {s t : Set M} (hs : IsPathConnected s) (ht : IsPathConnected t) : IsPathCon
nected (s * t)
参数：hs : IsPathConnected s；ht : IsPathConnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `JoinedIn.mul`：JoinedIn.mul {M : Type*} [Mul M] [TopologicalSpace M] [Con
tinuousMul M] {s t : Set M} {a b c d : M} (hs : JoinedIn s a b) (ht : JoinedIn t
 c…
-/
theorem IsPathConnected.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {s t : Set M} (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s * t) :=
  let ⟨a, ha_mem, ha⟩ := hs; let ⟨b, hb_mem, hb⟩ := ht
  ⟨a * b, mul_mem_mul ha_mem hb_mem, Set.forall_mem_image2.2 fun _x hx _y hy ↦ (ha hx).mul (hb hy)⟩

@[to_additive]
/-
**IsPathConnected.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [Co
ntinuousInv G] {s : Set G} (hs : IsPathConnected s) : IsPathConnected s⁻¹
参数：hs : IsPathConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inv_mem_inv`：inv_mem_inv : a⁻¹ in s⁻¹ ↔ a in s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `JoinedIn.map`：JoinedIn.map (h : JoinedIn F x y) {f : X -> Y} (hf : Conti
nuous f) : JoinedIn (f '' F) (f x) (f y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inv`：mem_inv : a in s⁻¹ ↔ a⁻¹ in s
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem IsPathConnected.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
    {s : Set G} (hs : IsPathConnected s) :
    IsPathConnected s⁻¹ :=
  let ⟨a, ha_mem, ha⟩ := hs
  ⟨a⁻¹, inv_mem_inv.mpr ha_mem, fun x hx ↦ by simpa using ha (mem_inv.mp hx) |>.map continuous_inv⟩

/-- If `f : X → Y` is an inducing map, `f(F)` is path-connected iff `F` is. -/
nonrec theorem Topology.IsInducing.isPathConnected_iff {f : X → Y} (hf : IsInducing f) :
    IsPathConnected F ↔ IsPathConnected (f '' F) := by
  simp only [IsPathConnected, forall_mem_image, exists_mem_image]
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ forall₂_congr fun y hy ↦ ?_
  rw [hf.joinedIn_image hx hy]

/-- If `h : X → Y` is a homeomorphism, `h(s)` is path-connected iff `s` is. -/
@[simp]
/-
**Homeomorph.isPathConnected_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.isPathConnected_image {s : Set X} (h : X ≃ₜ Y) : IsPathConnecte
d (h '' s) ↔ IsPathConnected s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsInducing.isPathConnected_iff`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {F : Set X} {f : X → 
Y},   Topology.IsInducing f →…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h

--- 原说明 ---
If `h : X → Y` is a homeomorphism, `h(s)` is path-connected iff `s` is.
-/
theorem Homeomorph.isPathConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPathConnected (h '' s) ↔ IsPathConnected s :=
  h.isInducing.isPathConnected_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is path-connected iff `s` is. -/
@[simp]
/-
**Homeomorph.isPathConnected_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.isPathConnected_preimage {s : Set Y} (h : X ≃ₜ Y) : IsPathConne
cted (h ⁻¹' s) ↔ IsPathConnected s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.isPathConnected_image`：Homeomorph.isPathConnected_image {s : 
Set X} (h : X ≃ₜ Y) : IsPathConnected (h '' s) ↔ IsPathConnected s

--- 原说明 ---
If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is path-connected iff `s` is.
-/
theorem Homeomorph.isPathConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPathConnected (h ⁻¹' s) ↔ IsPathConnected s := by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image
/-
**IsPathConnected.mem_pathComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x in F) 
(y_in : y in F) : y in pathComponent x
参数：h : IsPathConnected F；x_in : x in F；y_in : y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.joined`：JoinedIn.joined (h : JoinedIn F x y) : Joined x y
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y
-/
theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
    y ∈ pathComponent x :=
  (h.joinedIn x x_in y y_in).joined
/-
**IsPathConnected.subset_pathComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x in 
F) : F subseteq pathComponent x
参数：h : IsPathConnected F；x_in : x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.mem_pathComponent`：IsPathConnected.mem_pathComponent (h 
: IsPathConnected F) (x_in : x in F) (y_in : y in F) : y in pathComponent x
-/
theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) :
    F ⊆ pathComponent x := fun _y y_in => h.mem_pathComponent x_in y_in
/-
**IsPathConnected.subset_pathComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.subset_pathComponentIn {s : Set X} (hs : IsPathConnected s
) (hxs : x in s) (hsF : s subseteq F) : s subseteq pathComponentIn F x
参数：hs : IsPathConnected s；hxs : x in s；hsF : s subseteq F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.mono`：JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U
 subseteq V) : JoinedIn V x y
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y
-/
theorem IsPathConnected.subset_pathComponentIn {s : Set X} (hs : IsPathConnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ pathComponentIn F x :=
  fun y hys ↦ (hs.joinedIn x hxs y hys).mono hsF
/-
**isPathConnected_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.refl`：JoinedIn.refl (h : x in F) : JoinedIn F x x
-/
theorem isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X) := by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl
/-
**isPathConnected_pathComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_pathComponentIn (h : x in F) : IsPathConnected (pathCompon
entIn F x)
参数：h : x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_pathComponentIn_self`：mem_pathComponentIn_self (h : x in F) : x in p
athComponentIn F x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.extend_zero`：extend_zero : γ.extend 0 = x
· 使用定理 `Path.extend_extends'`：extend_extends' {a b : X} (γ : Path a b) (t : (Icc
 0 1 : Set Real)) : γ.extend t = γ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem isPathConnected_pathComponentIn (h : x ∈ F) : IsPathConnected (pathComponentIn F x) :=
  ⟨x, mem_pathComponentIn_self h, fun _ ⟨γ, hγ⟩ ↦ by
    refine ⟨γ, fun t ↦
      ⟨(γ.truncateOfLE t.2.1).cast (γ.extend_zero.symm) (γ.extend_extends' t).symm, fun t' ↦ ?_⟩⟩
    dsimp [Path.truncateOfLE, Path.truncate]
    exact γ.extend_extends' ⟨min (max t'.1 0) t.1, by simp [t.2.1, t.2.2]⟩ ▸ hγ _⟩
/-
**isPathConnected_pathComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_pathComponent : IsPathConnected (pathComponent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pathComponentIn_univ`：pathComponentIn_univ (x : X) : pathComponentIn uni
v x = pathComponent x
· 使用定理 `isPathConnected_pathComponentIn`：isPathConnected_pathComponentIn (h : x 
in F) : IsPathConnected (pathComponentIn F x)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem isPathConnected_pathComponent : IsPathConnected (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isPathConnected_pathComponentIn (mem_univ x)
/-
**IsPathConnected.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathC
onnected V) (hUV : (U inter V).Nonempty) : IsPathConnected (U union V)
参数：hU : IsPathConnected U；hV : IsPathConnected V；hUV : (U inter V).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.mono`：JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U
 subseteq V) : JoinedIn V x y
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U ∩ V).Nonempty) : IsPathConnected (U ∪ V) := by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
/-
**IsPathConnected.preimage_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU :
 W subseteq U) : IsPathConnected (((↑) : U -> X) ⁻¹' W)
参数：hW : IsPathConnected W；hWU : W subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isPathConnected_iff`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {F : Set X} {f : X → 
Y},   Topology.IsInducing f →…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s

--- 原说明 ---
If a set `W` is path-connected, then it is also path-connected when seen as a se
t in a smaller
ambient type `U` (when `U` contains `W`).
-/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
    IsPathConnected (((↑) : U → X) ⁻¹' W) := by
  rwa [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_val, inter_eq_right.2 hWU]

set_option backward.isDefEq.respectTransparency false in
/-
**IsPathConnected.exists_path_through_family** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.exists_path_through_family {n : Nat} {s : Set X} (h : IsPa
thConnected s) (p : Fin (n + 1) -> X) (hp : forall i, p i in s) : exists γ : Pat
h (p 0) (p (last n)), range γ subseteq s ∧ forall i, p i in range γ
参数：h : IsPathConnected s；p : Fin (n + 1) -> X；hp : forall i, p i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用引理 `Path.exists_congr`：exists_congr {x₁ x₂ y₁ y₂ : X} {p : Path x₁ y₁ -> Pro
p} (hx : x₁ = x₂) (hy : y₁ = y₂) : (exists γ, p γ) ↔ (exists (γ : Path x₂ y₂), p
 (γ.cas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Path.refl_range`：refl_range {a : X} : range (Path.refl a) = {a}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Fin.snoc_apply_zero`：snoc_apply_zero [NeZero n] : snoc p x 0 = p 0
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y
· 使用定理 `Path.trans_range`：trans_range {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c
) : range (γ₁.trans γ₂) = range γ₁ union range γ₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem IsPathConnected.exists_path_through_family {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ γ : Path (p 0) (p (last n)), range γ ⊆ s ∧ ∀ i, p i ∈ range γ := by
  cases p using snocCases with | _ p x => ?_
  simp only [forall_fin_succ', snoc_castSucc, snoc_last, Path.cast_coe,
    Path.target_mem_range, and_true] at hp ⊢
  obtain ⟨hp, hx⟩ := hp
  induction p using snocInduction generalizing x with
  | elim0 =>
    simp only [snoc_zero]
    use Path.refl x
    simp [hx]
  | @snoc n p y hp₂ =>
    simp only [forall_fin_succ', snoc_castSucc, snoc_last, snoc_apply_zero, Path.cast_coe] at hp ⊢
    obtain ⟨hp, hy⟩ := hp
    specialize hp₂ y hp hy
    obtain ⟨γ₀, hγ₀s, hγ₀p⟩ := hp₂
    obtain ⟨γ₁, hγ₁⟩ := h.joinedIn y hy x hx
    rw [← range_subset_iff] at hγ₁
    use γ₀.trans γ₁
    simp only [Path.trans_range, mem_union, Path.source_mem_range, or_true, and_true,
      union_subset_iff]
    tauto
/-
**IsPathConnected.exists_path_through_family'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.exists_path_through_family' {n : Nat} {s : Set X} (h : IsP
athConnected s) (p : Fin (n + 1) -> X) (hp : forall i, p i in s) : exists (γ : P
ath (p 0) (p (last n))) (t : Fin (n + 1) -> I), (forall t, γ t in s) ∧ forall i,
 γ (t i) = p i
参数：h : IsPathConnected s；p : Fin (n + 1) -> X；hp : forall i, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPathConnected.exists_path_through_family`：IsPathConnected.exists_path_
through_family {n : Nat} {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) ->
 X) (hp : forall i, p i in s) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsPathConnected.exists_path_through_family' {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ (γ : Path (p 0) (p (last n))) (t : Fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i := by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_ofPred_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

/-! ### Path connected spaces -/


/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
@[mk_iff]
/-
**PathConnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_4) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is path-connected if it is non-empty and every two points ca
n be
joined by a continuous path.
-/
class PathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A path-connected space must be nonempty. -/
  nonempty : Nonempty X
  /-- Any two points in a path-connected space must be joined by a continuous path. -/
  joined : ∀ x y : X, Joined x y
/-
**pathConnectedSpace_iff_zerothHomotopy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathConnectedSpace_iff_zerothHomotopy : PathConnectedSpace X ↔ Nonempty (Z
erothHomotopy X) ∧ Subsingleton (ZerothHomotopy X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_quotient_iff`：nonempty_quotient_iff (s : Setoid α) : Nonempty (
Quotient s) ↔ Nonempty α
· 使用定理 `PathConnectedSpace.nonempty`：∀ {X : Type u_4} {inst : TopologicalSpace X
} [self : PathConnectedSpace X], Nonempty X
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `PathConnectedSpace.joined`：∀ {X : Type u_4} {inst : TopologicalSpace X} 
[self : PathConnectedSpace X] (x y : X), Joined x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  let := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
    exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact <| Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/-- Use path-connectedness to build a path between two points. -/
/-
**PathConnectedSpace.somePath** 是 Mathlib 中的一个定义，位于命名空间 `PathConnectedSpace`。
形式化陈述：somePath (x y : X) : Path x y
参数：x y : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PathConnectedSpace.joined`：∀ {X : Type u_4} {inst : TopologicalSpace X} 
[self : PathConnectedSpace X] (x y : X), Joined x y

--- 原说明 ---
Use path-connectedness to build a path between two points.
-/
def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)
/-
**PathConnectedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `PathConnectedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (ZerothHomotopy X) :=
  (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

end PathConnectedSpace

/-
**pathConnectedSpace_iff_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ
 : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) := by
  simp [pathConnectedSpace_iff, isPathConnected_iff, nonempty_iff_univ_nonempty]
/-
**isPathConnected_iff_pathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnected
Space F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `Topology.IsInducing.isPathConnected_iff`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {F : Set X} {f : X → 
Y},   Topology.IsInducing f →…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F := by
  rw [pathConnectedSpace_iff_univ, IsInducing.subtypeVal.isPathConnected_iff, image_univ,
    Subtype.range_val_subtype, ofPred_mem_eq]
/-
**isPathConnected_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set 
X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
-/
theorem isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance
/-
**isPathConnected_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPathConnected_range [PathConnectedSpace X] {f : X -> Y} (hf : Continuous
 f) : IsPathConnected (range f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsPathConnected.image`：IsPathConnected.image (hF : IsPathConnected F) {f
 : X -> Y} (hf : Continuous f) : IsPathConnected (f '' F)
· 使用定理 `isPathConnected_univ`：isPathConnected_univ [PathConnectedSpace X] : IsPa
thConnected (univ : Set X)
-/
theorem isPathConnected_range [PathConnectedSpace X] {f : X → Y} (hf : Continuous f) :
    IsPathConnected (range f) := by
  rw [← image_univ]
  exact isPathConnected_univ.image hf
/-
**Function.Surjective.pathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.pathConnectedSpace [PathConnectedSpace X] {f : X -> Y}
 (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y
参数：hf : Surjective f；hf' : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `isPathConnected_range`：isPathConnected_range [PathConnectedSpace X] {f :
 X -> Y} (hf : Continuous f) : IsPathConnected (range f)
-/
theorem Function.Surjective.pathConnectedSpace [PathConnectedSpace X]
    {f : X → Y} (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ, ← hf.range_eq]
  exact isPathConnected_range hf'
/-
**Quotient.instPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] : Pa
thConnectedSpace (Quotient s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.pathConnectedSpace`：Function.Surjective.pathConnecte
dSpace [PathConnectedSpace X] {f : X -> Y} (hf : Surjective f) (hf' : Continuous
 f) : PathConnectedSpace Y
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
instance Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] :
    PathConnectedSpace (Quotient s) :=
  Quotient.mk'_surjective.pathConnectedSpace continuous_coinduced_rng

/-- This is a special case of `NormedSpace.instPathConnectedSpace` (and
`IsTopologicalAddGroup.pathConnectedSpace`). It exists only to simplify dependencies. -/
/-
**Real.instPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instPathConnectedSpace : PathConnectedSpace Real where joined x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
This is a special case of `NormedSpace.instPathConnectedSpace` (and
`IsTopologicalAddGroup.pathConnectedSpace`). It exists only to simplify dependen
cies.
-/
instance Real.instPathConnectedSpace : PathConnectedSpace ℝ where
  joined x y := ⟨⟨⟨fun (t : I) ↦ (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

/-! ### Products and pi types -/

section Prod

variable {s : Set X} {t : Set Y}

/-- If `x₁` is joined to `x₂` and `y₁` is joined to `y₂`, then `(x₁, y₁)` is joined to
`(x₂, y₂)` in the product space. -/
/-
**Joined.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : Joined x₁ x₂) (hy : Joined y₁ y₂
) : Joined (x₁, y₁) (x₂, y₂)
参数：hx : Joined x₁ x₂；hy : Joined y₁ y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x₁` is joined to `x₂` and `y₁` is joined to `y₂`, then `(x₁, y₁)` is joined 
to
`(x₂, y₂)` in the product space.
-/
theorem Joined.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : Joined x₁ x₂) (hy : Joined y₁ y₂) :
    Joined (x₁, y₁) (x₂, y₂) :=
  ⟨hx.somePath.prod hy.somePath⟩

/-- If `x₁` is joined to `x₂` within `s` and `y₁` to `y₂` within `t`, then `(x₁, y₁)` is joined
to `(x₂, y₂)` within `s ×ˢ t`. -/
/-
**JoinedIn.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : JoinedIn s x₁ x₂) (hy : Joined
In t y₁ y₂) : JoinedIn (s ×ˢ t) (x₁, y₁) (x₂, y₂)
参数：hx : JoinedIn s x₁ x₂；hy : JoinedIn t y₁ y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `x₁` is joined to `x₂` within `s` and `y₁` to `y₂` within `t`, then `(x₁, y₁)
` is joined
to `(x₂, y₂)` within `s ×ˢ t`.
-/
theorem JoinedIn.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : JoinedIn s x₁ x₂) (hy : JoinedIn t y₁ y₂) :
    JoinedIn (s ×ˢ t) (x₁, y₁) (x₂, y₂) :=
  ⟨hx.somePath.prod hy.somePath, by simp⟩

/-- The path component of `(x, y)` in the product space is the product of the path components
of `x` and `y`. -/
/-
**pathComponent_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent_prod (x : X) (y : Y) : pathComponent (x, y) = pathComponent 
x ×ˢ pathComponent y
参数：x : X；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Joined.map`：Joined.map {x y : X} {f : X -> Y} (h : Joined x y) (hf : Con
tinuous f) : Joined (f x) (f y)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Joined.prod`：Joined.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : Joined x₁ x₂) (hy
 : Joined y₁ y₂) : Joined (x₁, y₁) (x₂, y₂)

--- 原说明 ---
The path component of `(x, y)` in the product space is the product of the path c
omponents
of `x` and `y`.
-/
theorem pathComponent_prod (x : X) (y : Y) :
    pathComponent (x, y) = pathComponent x ×ˢ pathComponent y := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, mem_pathComponent_iff]
  exact ⟨fun h ↦ ⟨h.map continuous_fst, h.map continuous_snd⟩, fun ⟨h₁, h₂⟩ ↦ h₁.prod h₂⟩

/-- The product of two path-connected sets is path-connected. -/
/-
**IsPathConnected.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.prod (hs : IsPathConnected s) (ht : IsPathConnected t) : I
sPathConnected (s ×ˢ t)
参数：hs : IsPathConnected s；ht : IsPathConnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPathConnected_iff`：isPathConnected_iff : IsPathConnected F ↔ F.Nonempt
y ∧ forallᵉ (x in F) (y in F), JoinedIn F x y
· 使用定理 `Set.Nonempty.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `IsPathConnected.nonempty`：IsPathConnected.nonempty (h : IsPathConnected 
F) : F.Nonempty
· 使用定理 `JoinedIn.prod`：JoinedIn.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : JoinedIn s x₁
 x₂) (hy : JoinedIn t y₁ y₂) : JoinedIn (s ×ˢ t) (x₁, y₁) (x₂, y₂)
· 使用定理 `IsPathConnected.joinedIn`：IsPathConnected.joinedIn (h : IsPathConnected 
F) : forallᵉ (x in F) (y in F), JoinedIn F x y

--- 原说明 ---
The product of two path-connected sets is path-connected.
-/
theorem IsPathConnected.prod (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s ×ˢ t) := by
  rw [isPathConnected_iff]
  refine ⟨hs.nonempty.prod ht.nonempty, fun (x₁, y₁) ⟨hx₁, hy₁⟩ (x₂, y₂) ⟨hx₂, hy₂⟩ ↦ ?_⟩
  exact hs.joinedIn x₁ hx₁ x₂ hx₂ |>.prod <| ht.joinedIn y₁ hy₁ y₂ hy₂
/-
**Prod.instPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instPathConnectedSpace [PathConnectedSpace X] [PathConnectedSpace Y] 
: PathConnectedSpace (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `IsPathConnected.prod`：IsPathConnected.prod (hs : IsPathConnected s) (ht 
: IsPathConnected t) : IsPathConnected (s ×ˢ t)
· 使用定理 `isPathConnected_univ`：isPathConnected_univ [PathConnectedSpace X] : IsPa
thConnected (univ : Set X)
-/
instance Prod.instPathConnectedSpace [PathConnectedSpace X] [PathConnectedSpace Y] :
    PathConnectedSpace (X × Y) := by
  rw [pathConnectedSpace_iff_univ, ← Set.univ_prod_univ]
  exact isPathConnected_univ.prod isPathConnected_univ

end Prod

section Pi

variable {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]

/-- If for each `i`, `x i` is joined to `y i`, then `x` is joined to `y` in the product space. -/
/-
**Joined.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Joined.pi {x y : forall i, Z i} (h : forall i, Joined (x i) (y i)) : Joine
d x y
参数：h : forall i, Joined (x i) (y i)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If for each `i`, `x i` is joined to `y i`, then `x` is joined to `y` in the prod
uct space.
-/
theorem Joined.pi {x y : ∀ i, Z i} (h : ∀ i, Joined (x i) (y i)) : Joined x y :=
  ⟨.pi fun i ↦ (h i).somePath⟩

/-- If for each `i`, `x i` is joined to `y i` within `s i`, then `x` is joined to `y` within the
product set `Set.univ.pi s`. -/
/-
**JoinedIn.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.pi {s : forall i, Set (Z i)} {x y : forall i, Z i} (h : forall i,
 JoinedIn (s i) (x i) (y i)) : JoinedIn (Set.univ.pi s) x y
参数：Z i；h : forall i, JoinedIn (s i) (x i) (y i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If for each `i`, `x i` is joined to `y i` within `s i`, then `x` is joined to `y
` within the
product set `Set.univ.pi s`.
-/
theorem JoinedIn.pi {s : ∀ i, Set (Z i)} {x y : ∀ i, Z i}
    (h : ∀ i, JoinedIn (s i) (x i) (y i)) : JoinedIn (Set.univ.pi s) x y :=
  ⟨.pi (fun i ↦ (h i).somePath), by simp⟩

/-- The path component of `x` in a product space is the product of the path components of its
coordinates. -/
/-
**pathComponent_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathComponent_pi (x : forall i, Z i) : pathComponent x = Set.univ.pi fun i
 => pathComponent (x i)
参数：x : forall i, Z i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Joined.map`：Joined.map {x y : X} {f : X -> Y} (h : Joined x y) (hf : Con
tinuous f) : Joined (f x) (f y)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Joined.pi`：Joined.pi {x y : forall i, Z i} (h : forall i, Joined (x i) (
y i)) : Joined x y

--- 原说明 ---
The path component of `x` in a product space is the product of the path componen
ts of its
coordinates.
-/
theorem pathComponent_pi (x : ∀ i, Z i) :
    pathComponent x = Set.univ.pi fun i ↦ pathComponent (x i) := by
  ext y
  simp only [Set.mem_univ_pi, mem_pathComponent_iff]
  exact ⟨fun h i ↦ h.map (continuous_apply i), fun h ↦ .pi h⟩

/-- The product of a family of path-connected sets is path-connected. -/
/-
**IsPathConnected.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.pi {s : forall i, Set (Z i)} (h : forall i, IsPathConnecte
d (s i)) : IsPathConnected (Set.univ.pi s)
参数：Z i；h : forall i, IsPathConnected (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `JoinedIn.pi`：JoinedIn.pi {s : forall i, Set (Z i)} {x y : forall i, Z i}
 (h : forall i, JoinedIn (s i) (x i) (y i)) : JoinedIn (Set.univ.pi s) x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The product of a family of path-connected sets is path-connected.
-/
theorem IsPathConnected.pi {s : ∀ i, Set (Z i)} (h : ∀ i, IsPathConnected (s i)) :
    IsPathConnected (Set.univ.pi s) := by
  choose x hx hjoin using h
  exact ⟨x, by simpa, fun y hy ↦ .pi fun i ↦ hjoin i (by grind)⟩
/-
**Pi.instPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instPathConnectedSpace [forall i, PathConnectedSpace (Z i)] : PathConne
ctedSpace (forall i, Z i)
参数：Z i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `IsPathConnected.pi`：IsPathConnected.pi {s : forall i, Set (Z i)} (h : fo
rall i, IsPathConnected (s i)) : IsPathConnected (Set.univ.pi s)
· 使用定理 `isPathConnected_univ`：isPathConnected_univ [PathConnectedSpace X] : IsPa
thConnected (univ : Set X)
-/
instance Pi.instPathConnectedSpace [∀ i, PathConnectedSpace (Z i)] :
    PathConnectedSpace (∀ i, Z i) := by
  rw [pathConnectedSpace_iff_univ, ← Set.pi_univ]
  exact .pi fun _ ↦ isPathConnected_univ

end Pi

/-
**pathConnectedSpace_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ exists x : X, pathCompo
nent x = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pathComponentIn_univ`：pathComponentIn_univ (x : X) : pathComponentIn uni
v x = pathComponent x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ ∃ x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  rcases isPathConnected_iff_eq.mp (pathConnectedSpace_iff_univ.mp ‹_›) with ⟨x, _x_in, hx⟩
  use x
  rw [← univ_subset_iff]
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x

/-- A path-connected set is connected.

(See `Counterexamples.TopologistsSineCurve` for the standard counterexample showing that the
converse is false.) -/
/-
**IsPathConnected.isConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F
参数：hF : IsPathConnected F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F

--- 原说明 ---
A path-connected set is connected.

(See `Counterexamples.TopologistsSineCurve` for the standard counterexample show
ing that the
converse is false.)
-/
theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F := by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/-
**PathConnectedSpace.exists_path_through_family** 是 Mathlib 中的一个定理，位于命名空间 `PathC
onnectedSpace`。
形式化陈述：exists_path_through_family {n : Nat} (p : Fin (n + 1) -> X) : exists γ : P
ath (p 0) (p (last n)), forall i, p i in range γ
参数：p : Fin (n + 1) -> X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPathConnected.exists_path_through_family`：IsPathConnected.exists_path_
through_family {n : Nat} {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) ->
 X) (hp : forall i, p i in s) : …
-/
theorem exists_path_through_family {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ γ : Path (p 0) (p (last n)), ∀ i, p i ∈ range γ := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩
/-
**PathConnectedSpace.exists_path_through_family'** 是 Mathlib 中的一个定理，位于命名空间 `Path
ConnectedSpace`。
形式化陈述：exists_path_through_family' {n : Nat} (p : Fin (n + 1) -> X) : exists (γ :
 Path (p 0) (p (last n))) (t : Fin (n + 1) -> I), forall i, γ (t i) = p i
参数：p : Fin (n + 1) -> X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPathConnected.exists_path_through_family'`：IsPathConnected.exists_path
_through_family' {n : Nat} {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) 
-> X) (hp : forall i, p i in s) :…
-/
theorem exists_path_through_family' {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ (γ : Path (p 0) (p (last n))) (t : Fin (n + 1) → I), ∀ i, γ (t i) = p i := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

end PathConnectedSpace

/-- The preimage of a singleton in `ZerothHomotopy` is the path component of an element in the
equivalence class. -/
/-
**ZerothHomotopy.preimage_singleton_eq_pathComponent** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ZerothHomotopy.preimage_singleton_eq_pathComponent (x : X) : ZerothHomotop
y.mk ⁻¹' {.mk x} = pathComponent x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mem_pathComponent_iff`：mem_pathComponent_iff : x in pathComponent y ↔ Jo
ined y x
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y

--- 原说明 ---
The preimage of a singleton in `ZerothHomotopy` is the path component of an elem
ent in the
equivalence class.
-/
theorem ZerothHomotopy.preimage_singleton_eq_pathComponent (x : X) :
    ZerothHomotopy.mk ⁻¹' {.mk x} = pathComponent x := by
  ext y
  rw [mem_preimage, mem_singleton_iff, eq_comm, mem_pathComponent_iff]
  exact Quotient.eq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace X] : CompactSpace <| ZerothHomotopy X := Quotient.compactSpace

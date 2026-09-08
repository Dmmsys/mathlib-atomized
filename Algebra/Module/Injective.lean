/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Small.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Injective modules

## Main definitions

* `Module.Injective`: an `R`-module `Q` is injective if and only if every injective `R`-linear
  map descends to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `Module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an
  `Ideal R` extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `Module.Baer.injective`: an `R`-module is injective if it is Baer.

-/

@[expose] public section

assert_not_exists ModuleCat

noncomputable section

universe u v v'

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

/--
An `R`-module `Q` is injective if and only if every injective `R`-linear map descends to a linear
map to `Q`, i.e. in the following diagram, if `f` is injective then there is an `R`-linear map
`h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
-/
/-
**Module.Injective** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → [inst : Ring R] → (Q : Type v) → [inst_1 : AddCommGroup Q] 
→ [_root_.Module R Q] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `Q` is injective if and only if every injective `R`-linear map des
cends to a linear
map to `Q`, i.e. in the following diagram, if `f` is injective then there is an 
`R`-linear map
`h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
-/
@[mk_iff] class Module.Injective : Prop where
  out : ∀ ⦃X Y : Type v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) (_ : Function.Injective f) (g : X →ₗ[R] Q),
    ∃ h : Y →ₗ[R] Q, ∀ x, h (f x) = g x

/-- An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `Ideal R` extends to
an `R`-linear map `R ⟶ Q` -/
/-
**Module.Baer** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Baer : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `Idea
l R` extends to
an `R`-linear map `R ⟶ Q`
-/
def Module.Baer : Prop :=
  ∀ (I : Ideal R) (g : I →ₗ[R] Q), ∃ g' : R →ₗ[R] Q, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩

namespace Module.Baer

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

/-
**Module.Baer.of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module.Baer`。
形式化陈述：of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : Module.Baer R M
参数：e : Q ≃ₗ[R] M；h : Module.Baer R Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : Module.Baer R M := fun I g ↦
  have ⟨g', h'⟩ := h I (e.symm ∘ₗ g)
  ⟨e ∘ₗ g', by simpa [LinearEquiv.eq_symm_apply] using h'⟩
/-
**Module.Baer.congr** 是 Mathlib 中的一个引理，位于命名空间 `Module.Baer`。
形式化陈述：congr (e : Q ≃ₗ[R] M) : Module.Baer R Q ↔ Module.Baer R M
参数：e : Q ≃ₗ[R] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Baer.of_equiv`：of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : M
odule.Baer R M
-/
lemma congr (e : Q ≃ₗ[R] M) : Module.Baer R Q ↔ Module.Baer R M := ⟨of_equiv e, of_equiv e.symm⟩
/-
**Module.Baer.iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Module.Baer`。
形式化陈述：iff_surjective {R : Type u} [CommRing R] [Module R M] : Module.Baer R M ↔ 
forall (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma iff_surjective {R : Type u} [CommRing R] [Module R M] : Module.Baer R M ↔
    ∀ (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype) := by
  refine ⟨fun h I g ↦ ?_, fun h I g ↦ ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

/-- If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, then a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we need to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`. -/
/-
**Module.Baer.ExtensionOf** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module.Baer`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] → (M →ₗ[R] N) → (M →ₗ[R] Q)
 → Type (max u_2 v)
参数：M →ₗ[R] N；M →ₗ[R] Q；max u_2 v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, t
hen a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we ne
ed to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`.
-/
structure ExtensionOf extends N →ₗ.[R] Q where
  le : LinearMap.range i ≤ domain
  is_extension : ∀ m : M, f m = toLinearPMap ⟨i m, le ⟨m, rfl⟩⟩

section Ext

variable {i f}

@[ext (iff := false)]
/-
**Module.Baer.ExtensionOf.ext** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer.ExtensionOf
`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] {i : M →ₗ[R] N} {f : M →ₗ[R] Q} {a b : Module.Baer.ExtensionOf i f},   
a.domain = b.domain →     (∀ ⦃x : N⦄ ⦃ha : x ∈ a.domain⦄ ⦃hb : x ∈ b.domain⦄, ↑a
.toLinearPMap ⟨x, ha⟩ = ↑b.toLinearPMap ⟨x, hb⟩) → a = b
参数：∀ ⦃x : N⦄ ⦃ha : x ∈ a.domain⦄ ⦃hb : x ∈ b.domain⦄, ↑a.toLinearPMap ⟨x, ha⟩ = 
↑b.toLinearPMap ⟨x, hb⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.ext`：ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' :
 forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩
) : …
-/
theorem ExtensionOf.ext {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq : ∀ ⦃x : N⦄ ⦃ha : x ∈ a.domain⦄ ⦃hb : x ∈ b.domain⦄,
      a.toLinearPMap ⟨x, ha⟩ = b.toLinearPMap ⟨x, hb⟩) :
    a = b := by
  rcases a with ⟨a, a_le, e1⟩
  congr
  exact LinearPMap.ext domain_eq to_fun_eq

/-- A dependent version of `ExtensionOf.ext` -/
/-
**Module.Baer.ExtensionOf.dExt** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer.ExtensionO
f`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] {i : M →ₗ[R] N} {f : M →ₗ[R] Q} {a b : Module.Baer.ExtensionOf i f},   
a.domain = b.domain → (∀ ⦃x : ↥a.domain⦄ ⦃y : ↥b.domain⦄, ↑x = ↑y → ↑a.toLinearP
Map x = ↑b.toLinearPMap y) → a = b
参数：∀ ⦃x : ↥a.domain⦄ ⦃y : ↥b.domain⦄, ↑x = ↑y → ↑a.toLinearPMap x = ↑b.toLinearP
Map y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.ExtensionOf.ext`：∀ {R : Type u} [inst : Ring R] {Q : Type v}
 [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : Ty
pe u_2} [inst_3 :…

--- 原说明 ---
A dependent version of `ExtensionOf.ext`
-/
theorem ExtensionOf.dExt {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq :
      ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄, (x : N) = y → a.toLinearPMap x = b.toLinearPMap y) :
    a = b :=
  ext domain_eq fun _ _ _ ↦ to_fun_eq rfl
/-
**Module.Baer.ExtensionOf.dExt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer.Extens
ionOf`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] {i : M →ₗ[R] N} {f : M →ₗ[R] Q} {a b : Module.Baer.ExtensionOf i f},   
a = b ↔     ∃ (_ : a.domain = b.domain), ∀ ⦃x : ↥a.domain⦄ ⦃y : ↥b.domain⦄, ↑x =
 ↑y → ↑a.toLinearPMap x = ↑b.toLinearPMap y
参数：_ : a.domain = b.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Baer.ExtensionOf.dExt`：∀ {R : Type u} [inst : Ring R] {Q : Type v
} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : T
ype u_2} [inst_3 :…
-/
theorem ExtensionOf.dExt_iff {a b : ExtensionOf i f} :
    a = b ↔ ∃ _ : a.domain = b.domain, ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄,
    (x : N) = y → a.toLinearPMap x = b.toLinearPMap y :=
  ⟨fun r => r ▸ ⟨rfl, fun _ _ h => congr_arg a.toFun <| mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.dExt h1 h2⟩
/-
**Module.Baer.ExtensionOf.toLinearPMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.Baer.ExtensionOf`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] {i : M →ₗ[R] N} {f : M →ₗ[R] Q}, Function.Injective Module.Baer.Extensi
onOf.toLinearPMap
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.ExtensionOf.ext`：∀ {R : Type u} [inst : Ring R] {Q : Type v}
 [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : Ty
pe u_2} [inst_3 :…
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ExtensionOf.toLinearPMap_injective :
    Function.Injective (α := ExtensionOf i f) ExtensionOf.toLinearPMap :=
  fun _ _ _ ↦ by ext <;> congr!

end Ext

/-
**Module.Baer.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Baer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (ExtensionOf i f) where
  min X1 X2 :=
    { X1.toLinearPMap ⊓ X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), ?_⟩
          rw [← X1.is_extension x, ← X2.is_extension x] :
          x ∈ X1.toLinearPMap.eqLocus X2.toLinearPMap)
      is_extension := fun _ => X1.is_extension _ }
/-
**Module.Baer.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Baer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ExtensionOf i f) :=
  PartialOrder.lift _ ExtensionOf.toLinearPMap_injective
/-
**Module.Baer.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Baer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (ExtensionOf i f) :=
  ExtensionOf.toLinearPMap_injective.semilatticeInf _
    .rfl .rfl fun X Y ↦ LinearPMap.ext rfl fun x y h ↦ by congr

variable {i f}
/-
**Module.Baer.chain_linearPMap_of_chain_extensionOf** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Baer`。
形式化陈述：chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)} (hchain 
: IsChain (· <= ·) c) : IsChain (· <= ·) (fun x : ExtensionOf i f => x.toLinearP
Map) '' c
参数：ExtensionOf i f；hchain : IsChain (· <= ·) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· ≤ ·) c) :
    IsChain (· ≤ ·) <| (fun x : ExtensionOf i f => x.toLinearPMap) '' c := by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ ne
  exact hchain a_mem b_mem (ne_of_apply_ne _ ne)

/-- The maximal element of every nonempty chain of `extension_of i f`. -/
/-
**Module.Baer.ExtensionOf.max** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer.ExtensionOf
`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       {i 
: M →ₗ[R] N} →                         {f : M →ₗ[R] Q} →                        
   {c : Set (Module.Baer.ExtensionOf i f)} →                             IsChain
 (fun x1 x2 => x1 ≤ x2) c → c.Nonempty → Module.Baer.ExtensionOf i f
参数：Module.Baer.ExtensionOf i f；fun x1 x2 => x1 ≤ x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal element of every nonempty chain of `extension_of i f`.
-/
def ExtensionOf.max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) : ExtensionOf i f :=
  { LinearPMap.sSup _
      (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) with
    le := by
      refine le_trans hnonempty.some.le <|
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
      refine Eq.trans (hnonempty.some.is_extension m) ?_
      symm
      generalize_proofs _ _ h1
      exact
        LinearPMap.sSup_apply (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
          ((Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩) ⟨i m, h1⟩ }
/-
**Module.Baer.ExtensionOf.le_max** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer.Extensio
nOf`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] {i : M →ₗ[R] N} {f : M →ₗ[R] Q} {c : Set (Module.Baer.ExtensionOf i f)}
   (hchain : IsChain (fun x1 x2 => x1 ≤ x2) c) (hnonempty : c.Nonempty),   ∀ a ∈
 c, a ≤ Module.Baer.ExtensionOf.max hchain hnonempty
参数：Module.Baer.ExtensionOf i f；hchain : IsChain (fun x1 x2 => x1 ≤ x2) c；hnonemp
ty : c.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.le_sSup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [ins
t_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 :
 _root_.…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Module.Baer.chain_linearPMap_of_chain_extensionOf`：chain_linearPMap_of_c
hain_extensionOf {c : Set (ExtensionOf i f)} (hchain : IsChain (· <= ·) c) : IsC
hain (· <= ·) (fun x : ExtensionOf i f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem ExtensionOf.le_max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) (a : ExtensionOf i f) (ha : a ∈ c) :
    a ≤ ExtensionOf.max hchain hnonempty :=
  LinearPMap.le_sSup (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) <|
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩

variable (i f) [Fact <| Function.Injective i]
/-
**Module.Baer.ExtensionOf.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer.Exten
sionOf`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) →                         (f : M →ₗ[R] Q) → [Fact (Function.Injecti
ve ⇑i)] → Inhabited (Module.Baer.ExtensionOf i f)
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；Module.Baer.ExtensionOf i f
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ExtensionOf.inhabited : Inhabited (ExtensionOf i f) where
  default :=
    { domain := LinearMap.range i
      toFun :=
        { toFun := fun x => f x.2.choose
          map_add' := fun x y => by
            have eq1 : _ + _ = (x + y).1 := congr_arg₂ (· + ·) x.2.choose_spec y.2.choose_spec
            rw [← map_add, ← (x + y).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1, map_add]
          map_smul' := fun r x => by
            have eq1 : r • _ = (r • x).1 := congr_arg (r • ·) x.2.choose_spec
            rw [← map_smul, ← (r • x).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1, map_smul] }
      le := le_refl _
      is_extension := fun m => by
        simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
        dsimp
        apply congrArg
        exact Fact.out (p := Function.Injective i)
          (⟨i m, ⟨_, rfl⟩⟩ : LinearMap.range i).2.choose_spec.symm }

/-- Since every nonempty chain has a maximal element, by Zorn's lemma, there is a maximal
`extension_of i f`. -/
/-
**Module.Baer.extensionOfMax** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer`。
形式化陈述：extensionOfMax : ExtensionOf i f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since every nonempty chain has a maximal element, by Zorn's lemma, there is a ma
ximal
`extension_of i f`.
-/
def extensionOfMax : ExtensionOf i f :=
  (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose
/-
**Module.Baer.extensionOfMax_is_max** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`。
形式化陈述：extensionOfMax_is_max : forall (a : ExtensionOf i f), extensionOfMax i f <
= a -> a = extensionOfMax i f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.eq_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → b = a
· 使用定理 `zorn_le_nonempty`：zorn_le_nonempty [Nonempty α] (h : forall c : Set α, I
sChain (· <= ·) c -> c.Nonempty -> BddAbove c) : exists m : α, IsMax m
· 使用定理 `Module.Baer.ExtensionOf.le_max`：∀ {R : Type u} [inst : Ring R] {Q : Type
 v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N :
 Type u_2} [inst_3 :…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem extensionOfMax_is_max :
    ∀ (a : ExtensionOf i f), extensionOfMax i f ≤ a → a = extensionOfMax i f :=
  fun _ ↦ (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
    ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec.eq_of_ge

-- Auxiliary definition: Lean looks for an instance of `Max (Type u)` if we would write
-- `(x : (extensionOfMax i f).domain ⊔ (Submodule.span R {y}))`, so we encapsulate the cast instead.
/-
**Module.Baer.supExtensionOfMaxSingleton** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.Bae
r`。
形式化陈述：supExtensionOfMaxSingleton (y : N) : Submodule R N
参数：y : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev supExtensionOfMaxSingleton (y : N) : Submodule R N :=
  (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

variable {f}

set_option backward.privateInPublic true in
/-
**Module.Baer.extensionOfMax_adjoin.aux1** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`. -/
/-
**Module.Baer.ExtensionOfMaxAdjoin.fst** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer.Ex
tensionOfMaxAdjoin`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) →                         {f : M →ₗ[R] Q} →                        
   [inst_7 : Fact (Function.Injective ⇑i)] →                             {y : N}
 →                               ↥(Module.Baer.supExtensionOfMaxSingleton i f y)
 → ↥(Module.Baer.extensionOfMax i f).domain
参数：i : M →ₗ[R] N；Function.Injective ⇑i；Module.Baer.supExtensionOfMaxSingleton i 
f y；Module.Baer.extensionOfMax i f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Module.Injective.0.Module.Baer.extensionOfMax_a
djoin.aux1`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q
] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 :…

--- 原说明 ---
If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`.
-/
def ExtensionOfMaxAdjoin.fst {y : N} (x : supExtensionOfMaxSingleton i f y) :
    (extensionOfMax i f).domain :=
  (extensionOfMax_adjoin.aux1 i x).choose

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`. -/
/-
**Module.Baer.ExtensionOfMaxAdjoin.snd** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer.Ex
tensionOfMaxAdjoin`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) →                         {f : M →ₗ[R] Q} →                        
   [inst_7 : Fact (Function.Injective ⇑i)] →                             {y : N}
 → ↥(Module.Baer.supExtensionOfMaxSingleton i f y) → R
参数：i : M →ₗ[R] N；Function.Injective ⇑i；Module.Baer.supExtensionOfMaxSingleton i 
f y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Module.Injective.0.Module.Baer.extensionOfMax_a
djoin.aux1`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q
] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 :…

--- 原说明 ---
If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`.
-/
def ExtensionOfMaxAdjoin.snd {y : N} (x : supExtensionOfMaxSingleton i f y) : R :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose
/-
**Module.Baer.ExtensionOfMaxAdjoin.eqn** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer.Ex
tensionOfMaxAdjoin`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] (i : M →ₗ[R] N) {f : M →ₗ[R] Q} [inst_7 : Fact (Function.Injective ⇑i)]
 {y : N}   (x : ↥(Module.Baer.supExtensionOfMaxSingleton i f y)),   ↑x = ↑(Modul
e.Baer.ExtensionOfMaxAdjoin.fst i x) + Module.Baer.ExtensionOfMaxAdjoin.snd i x 
• y
参数：i : M →ₗ[R] N；Function.Injective ⇑i；x : ↥(Module.Baer.supExtensionOfMaxSingle
ton i f y)；Module.Baer.ExtensionOfMaxAdjoin.fst i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `_private.Mathlib.Algebra.Module.Injective.0.Module.Baer.extensionOfMax_a
djoin.aux1`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q
] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 :…
-/
theorem ExtensionOfMaxAdjoin.eqn {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ↑x = ↑(ExtensionOfMaxAdjoin.fst i x) + ExtensionOfMaxAdjoin.snd i x • y :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose_spec

variable (f)

-- TODO: refactor to use colon ideals?
/-- The ideal `I = {r | r • y ∈ N}` -/
/-
**Module.Baer.ExtensionOfMaxAdjoin.ideal** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer.
ExtensionOfMaxAdjoin`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) → (M →ₗ[R] Q) → [Fact (Function.Injective ⇑i)] → N → Ideal R
参数：i : M →ₗ[R] N；M →ₗ[R] Q；Function.Injective ⇑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal `I = {r | r • y ∈ N}`
-/
def ExtensionOfMaxAdjoin.ideal (y : N) : Ideal R :=
  (extensionOfMax i f).domain.comap ((LinearMap.id : R →ₗ[R] R).smulRight y)

/-- A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension -/
/-
**Module.Baer.ExtensionOfMaxAdjoin.idealTo** 是 Mathlib 中的一个定义，位于命名空间 `Module.Bae
r.ExtensionOfMaxAdjoin`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) →                         (f : M →ₗ[R] Q) →                        
   [inst_7 : Fact (Function.Injective ⇑i)] →                             (y : N)
 → ↥(Module.Baer.ExtensionOfMaxAdjoin.ideal i f y) →ₗ[R] Q
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；y : N；Module.Baer.Extension
OfMaxAdjoin.ideal i f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension
-/
def ExtensionOfMaxAdjoin.idealTo (y : N) : ExtensionOfMaxAdjoin.ideal i f y →ₗ[R] Q where
  toFun (z : { x // x ∈ ideal i f y }) := (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.prop⟩
  map_add' (z1 z2 : { x // x ∈ ideal i f y }) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    congr
    apply add_smul
  map_smul' z1 (z2 : {x // x ∈ ideal i f y}) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_smul]
    congr 2
    apply mul_smul

/-- Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends to `R ⟶ Q`,
call this extended map `φ` -/
/-
**Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo** 是 Mathlib 中的一个定义，位于命名空间 `Modu
le.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) → (M →ₗ[R] Q) → [Fact (Function.Injective ⇑i)] → Module.Baer R Q → 
N → R →ₗ[R] Q
参数：i : M →ₗ[R] N；M →ₗ[R] Q；Function.Injective ⇑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends
 to `R ⟶ Q`,
call this extended map `φ`
-/
def ExtensionOfMaxAdjoin.extendIdealTo (h : Module.Baer R Q) (y : N) : R →ₗ[R] Q :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose
/-
**Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_is_extension** 是 Mathlib 中的一个定理
，位于命名空间 `Module.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q) [inst_7 : Fact (Function.Injective ⇑i)]
   (h : Module.Baer R Q) (y : N) (x : R) (mem : x ∈ Module.Baer.ExtensionOfMaxAd
join.ideal i f y),   (Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo i f h y) x 
= (Module.Baer.ExtensionOfMaxAdjoin.idealTo i f y) ⟨x, mem⟩
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；h : Module.Baer R Q；y : N；x
 : R；mem : x ∈ Module.Baer.ExtensionOfMaxAdjoin.ideal i f y；Module.Baer.Extensio
nOfMaxAdjoin.extendIdealTo i f h y；Module.Baer.ExtensionOfMaxAdjoin.idealTo i f 
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_is_extension (h : Module.Baer R Q) (y : N) :
    ∀ (x : R) (mem : x ∈ ExtensionOfMaxAdjoin.ideal i f y),
      ExtensionOfMaxAdjoin.extendIdealTo i f h y x = ExtensionOfMaxAdjoin.idealTo i f y ⟨x, mem⟩ :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec
/-
**Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd'** 是 Mathlib 中的一个定理，位于命名空间 `
Module.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q) [inst_7 : Fact (Function.Injective ⇑i)]
   (h : Module.Baer R Q) {y : N} (r : R), r • y = 0 → (Module.Baer.ExtensionOfMa
xAdjoin.extendIdealTo i f h y) r = 0
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；h : Module.Baer R Q；r : R；M
odule.Baer.ExtensionOfMaxAdjoin.extendIdealTo i f h y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_is_extension`：∀ {R : Type
 u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Modu
le R Q] {M : Type u_1}   {N : Type u_2} [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_wd' (h : Module.Baer R Q) {y : N} (r : R)
    (eq1 : r • y = 0) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r = 0 := by
  have : r ∈ ideal i f y := by
    change (r • y) ∈ (extensionOfMax i f).toLinearPMap.domain
    rw [eq1]
    apply Submodule.zero_mem _
  rw [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h y r this]
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  simp only [eq1, ← ZeroMemClass.zero_def, (extensionOfMax i f).toLinearPMap.map_zero]
/-
**Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q) [inst_7 : Fact (Function.Injective ⇑i)]
   (h : Module.Baer R Q) {y : N} (r r' : R),   r • y = r' • y →     (Module.Baer
.ExtensionOfMaxAdjoin.extendIdealTo i f h y) r =       (Module.Baer.ExtensionOfM
axAdjoin.extendIdealTo i f h y) r'
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；h : Module.Baer R Q；r r' : 
R；Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo i f h y；Module.Baer.ExtensionOf
MaxAdjoin.extendIdealTo i f h y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd'`：∀ {R : Type u} [inst
 : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {
M : Type u_1}   {N : Type u_2} [inst_3 :…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_wd (h : Module.Baer R Q) {y : N} (r r' : R)
    (eq1 : r • y = r' • y) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r' := by
  rw [← sub_eq_zero, ← map_sub]
  convert! ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  rw [sub_smul, sub_eq_zero, eq1]
/-
**Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q) [inst_7 : Fact (Function.Injective ⇑i)]
   (h : Module.Baer R Q) {y : N} (r : R) (hr : r • y ∈ (Module.Baer.extensionOfM
ax i f).domain),   (Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo i f h y) r = 
    ↑(Module.Baer.extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；h : Module.Baer R Q；r : R；h
r : r • y ∈ (Module.Baer.extensionOfMax i f).domain；Module.Baer.ExtensionOfMaxAd
join.extendIdealTo i f h y；Module.Baer.extensionOfMax i f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_is_extension`：∀ {R : Type
 u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Modu
le R Q] {M : Type u_1}   {N : Type u_2} [inst_3 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ExtensionOfMaxAdjoin.extendIdealTo_eq (h : Module.Baer R Q) {y : N} (r : R)
    (hr : r • y ∈ (extensionOfMax i f).domain) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    (extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩ := by
  simp only [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h _ _ hr,
    ExtensionOfMaxAdjoin.idealTo, LinearMap.coe_mk, AddHom.coe_mk]

/-- We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
/-
**Module.Baer.ExtensionOfMaxAdjoin.extensionToFun** 是 Mathlib 中的一个定义，位于命名空间 `Mod
ule.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {Q : Type v} →       [inst_1 : AddC
ommGroup Q] →         [inst_2 : _root_.Module R Q] →           {M : Type u_1} → 
            {N : Type u_2} →               [inst_3 : AddCommGroup M] →          
       [inst_4 : AddCommGroup N] →                   [inst_5 : _root_.Module R M
] →                     [inst_6 : _root_.Module R N] →                       (i 
: M →ₗ[R] N) →                         (f : M →ₗ[R] Q) →                        
   [inst_7 : Fact (Function.Injective ⇑i)] →                             Module.
Baer R Q → {y : N} → ↥(Module.Baer.supExtensionOfMaxSingleton i f y) → Q
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；Module.Baer.supExtensionOfM
axSingleton i f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
def ExtensionOfMaxAdjoin.extensionToFun (h : Module.Baer R Q) {y : N} :
    supExtensionOfMaxSingleton i f y → Q := fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)
/-
**Module.Baer.ExtensionOfMaxAdjoin.extensionToFun_wd** 是 Mathlib 中的一个定理，位于命名空间 `
Module.Baer.ExtensionOfMaxAdjoin`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q) [inst_7 : Fact (Function.Injective ⇑i)]
   (h : Module.Baer R Q) {y : N} (x : ↥(Module.Baer.supExtensionOfMaxSingleton i
 f y))   (a : ↥(Module.Baer.extensionOfMax i f).domain) (r : R),   ↑x = ↑a + r •
 y →     Module.Baer.ExtensionOfMaxAdjoin.extensionToFun i f h x =       ↑(Modul
e.Baer.extensionOfMax i f).toLinearPMap a + (Module.Baer.ExtensionOfMaxAdjoin.ex
tendIdealTo i f h y) r
参数：i : M →ₗ[R] N；f : M →ₗ[R] Q；Function.Injective ⇑i；h : Module.Baer R Q；x : ↥(M
odule.Baer.supExtensionOfMaxSingleton i f y)；a : ↥(Module.Baer.extensionOfMax i 
f).domain；r : R；Module.Baer.extensionOfMax i f；Module.Baer.ExtensionOfMaxAdjoin.
extendIdealTo i f h y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_sub_sub_eq`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 d : α), a - b - (c - d) = a + d - (b + c)
· 使用定理 `Module.Baer.ExtensionOfMaxAdjoin.eqn`：∀ {R : Type u} [inst : Ring R] {Q 
: Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1} 
  {N : Type u_2} [inst_3 :…
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_eq`：∀ {R : Type u} [inst 
: Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M
 : Type u_1}   {N : Type u_2} [inst_3 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LinearPMap.map_add`：map_add (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x +
 y) = f x + f y
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddMemClass.mk_add_mk`：∀ {M : Type u_1} {A : Type u_3} [inst : Add M] [i
nst_1 : SetLike A M] [hA : AddMemClass A M] (S' : A) (x y : M)   (hx : x ∈ S') (
hy : y ∈ S'…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
-/
theorem ExtensionOfMaxAdjoin.extensionToFun_wd (h : Module.Baer R Q) {y : N}
    (x : supExtensionOfMaxSingleton i f y) (a : (extensionOfMax i f).domain)
    (r : R) (eq1 : ↑x = ↑a + r • y) :
    ExtensionOfMaxAdjoin.extensionToFun i f h x =
      (extensionOfMax i f).toLinearPMap a + ExtensionOfMaxAdjoin.extendIdealTo i f h y r := by
  obtain ⟨a, ha⟩ := a
  have eq2 :
    (ExtensionOfMaxAdjoin.fst i x - a : N) = (r - ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    ExtensionOfMaxAdjoin.extendIdealTo_eq i f h (r - ExtensionOfMaxAdjoin.snd i x)
      (by rw [← eq2]; exact Submodule.sub_mem _ (ExtensionOfMaxAdjoin.fst i x).2 ha)
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3
  unfold ExtensionOfMaxAdjoin.extensionToFun
  rw [eq3, ← add_assoc, ← (extensionOfMax i f).toLinearPMap.map_add, AddMemClass.mk_add_mk]
  congr
  ext
  dsimp
  rw [Subtype.coe_mk, add_sub, ← eq1]
  exact eq_sub_of_add_eq (ExtensionOfMaxAdjoin.eqn i x).symm

/-- The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f` -/
/-
**Module.Baer.extensionOfMaxAdjoin** 是 Mathlib 中的一个定义，位于命名空间 `Module.Baer`。
形式化陈述：extensionOfMaxAdjoin (h : Module.Baer R Q) (y : N) : ExtensionOf i f where
 domain
参数：h : Module.Baer R Q；y : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f`
-/
def extensionOfMaxAdjoin (h : Module.Baer R Q) (y : N) : ExtensionOf i f where
  domain := supExtensionOfMaxSingleton i f y -- (extensionOfMax i f).domain ⊔ Submodule.span R {y}
  le := le_trans (extensionOfMax i f).le le_sup_left
  toFun :=
    { toFun := ExtensionOfMaxAdjoin.extensionToFun i f h
      map_add' := fun a b => by
        have eq1 :
          ↑a + ↑b =
            ↑(ExtensionOfMaxAdjoin.fst i a + ExtensionOfMaxAdjoin.fst i b) +
              (ExtensionOfMaxAdjoin.snd i a + ExtensionOfMaxAdjoin.snd i b) • y := by
          rw [ExtensionOfMaxAdjoin.eqn, ExtensionOfMaxAdjoin.eqn, add_smul, Submodule.coe_add]
          ac_rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd (y := y) i f h (a + b) _ _ eq1,
          LinearPMap.map_add, map_add]
        unfold ExtensionOfMaxAdjoin.extensionToFun
        abel
      map_smul' := fun r a => by
        dsimp
        have eq1 :
          r • (a : N) =
            ↑(r • ExtensionOfMaxAdjoin.fst i a) + (r • ExtensionOfMaxAdjoin.snd i a) • y := by
          rw [ExtensionOfMaxAdjoin.eqn, smul_add, smul_eq_mul, mul_smul]
          rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h (r • a :) _ _ eq1, map_smul,
          LinearPMap.map_smul, ← smul_add]
        congr }
  is_extension m := by
    dsimp
    rw [(extensionOfMax i f).is_extension,
      ExtensionOfMaxAdjoin.extensionToFun_wd i f h _ ⟨i m, _⟩ 0 _, map_zero, add_zero]
    simp
/-
**Module.Baer.extensionOfMax_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`。
形式化陈述：extensionOfMax_le (h : Module.Baer R Q) {y : N} : extensionOfMax i f <= ex
tensionOfMaxAdjoin i f h y
参数：h : Module.Baer R Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Baer.ExtensionOfMaxAdjoin.extensionToFun_wd`：∀ {R : Type u} [inst
 : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {
M : Type u_1}   {N : Type u_2} [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem extensionOfMax_le (h : Module.Baer R Q) {y : N} :
    extensionOfMax i f ≤ extensionOfMaxAdjoin i f h y :=
  ⟨le_sup_left, fun x x' EQ => by
    symm
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩
/-
**Module.Baer.extensionOfMax_to_submodule_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.Baer`。
形式化陈述：extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) : (extensionOfMax
 i f).domain = ⊤
参数：h : Module.Baer R Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Baer.extensionOfMax_is_max`：extensionOfMax_is_max : forall (a : E
xtensionOf i f), extensionOfMax i f <= a -> a = extensionOfMax i f
· 使用定理 `Module.Baer.extensionOfMax_le`：extensionOfMax_le (h : Module.Baer R Q) {
y : N} : extensionOfMax i f <= extensionOfMaxAdjoin i f h y
· 使用定理 `Module.Baer.extensionOfMaxAdjoin.eq_1`：∀ {R : Type u} [inst : Ring R] {Q
 : Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}
   {N : Type u_2} [inst_3 :…
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (extensionOfMax i f).domain = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h), extensionOfMaxAdjoin,
    Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩
/-
**Module.Baer.extension_property** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] {M : Type u_1}   {N : Type u_2} [inst_3 : AddCommGroup 
M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Mod
ule R N],   Module.Baer R Q → ∀ (f : M →ₗ[R] N), Function.Injective ⇑f → ∀ (g : 
M →ₗ[R] Q), ∃ h, h ∘ₗ f = g
参数：f : M →ₗ[R] N；g : M →ₗ[R] Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Baer.extensionOfMax_to_submodule_eq_top`：extensionOfMax_to_submod
ule_eq_top (h : Module.Baer R Q) : (extensionOfMax i f).domain = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.map_add`：map_add (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x +
 y) = f x + f y
· 使用定理 `LinearPMap.map_smul`：map_smul [Module R F] (f : E ->ₗ.[R] F) (c : R) (x 
: f.domain) : f (c • x) = c • f x
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Module.Baer.ExtensionOf.le`：∀ {R : Type u} [inst : Ring R] {Q : Type v} 
[inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N : Typ
e u_2} [inst_3 :…
· 使用定理 `Module.Baer.ExtensionOf.is_extension`：∀ {R : Type u} [inst : Ring R] {Q 
: Type v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1} 
  {N : Type u_2} [inst_3 :…
-/
protected theorem extension_property (h : Module.Baer R Q)
    (f : M →ₗ[R] N) (hf : Function.Injective f) (g : M →ₗ[R] Q) : ∃ h, h ∘ₗ f = g :=
  haveI : Fact (Function.Injective f) := ⟨hf⟩
  Exists.intro
    { toFun := ((extensionOfMax f g).toLinearPMap
        ⟨·, (extensionOfMax_to_submodule_eq_top f g h).symm ▸ ⟨⟩⟩)
      map_add' := fun x y ↦ by rw [← LinearPMap.map_add]; congr
      map_smul' := fun r x ↦ by rw [← LinearPMap.map_smul]; dsimp } <|
    LinearMap.ext fun x ↦ ((extensionOfMax f g).is_extension x).symm
/-
**Module.Baer.extension_property_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Baer`。
形式化陈述：extension_property_addMonoidHom (h : Module.Baer Int Q) (f : M ->+ N) (hf 
: Function.Injective f) (g : M ->+ Q) : exists h : N ->+ Q, h.comp f = g
参数：h : Module.Baer Int Q；f : M ->+ N；hf : Function.Injective f；g : M ->+ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.extension_property`：∀ {R : Type u} [inst : Ring R] {Q : Type
 v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N :
 Type u_2} [inst_3 :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem extension_property_addMonoidHom (h : Module.Baer ℤ Q)
    (f : M →+ N) (hf : Function.Injective f) (g : M →+ Q) : ∃ h : N →+ Q, h.comp f = g :=
  have ⟨g', hg'⟩ := h.extension_property f.toIntLinearMap hf g.toIntLinearMap
  ⟨g', congr(LinearMap.toAddMonoidHom $hg')⟩

/-- **Baer's criterion** for injective module : a Baer module is an injective module, i.e. if every
linear map from an ideal can be extended, then the module is injective. -/
/-
**Module.Baer.injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q],   Module.Baer R Q → Module.Injective R Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.extension_property`：∀ {R : Type u} [inst : Ring R] {Q : Type
 v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N :
 Type u_2} [inst_3 :…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
**Baer's criterion** for injective module : a Baer module is an injective module
, i.e. if every
linear map from an ideal can be extended, then the module is injective.
-/
protected theorem injective (h : Module.Baer R Q) : Module.Injective R Q where
  out X Y _ _ _ _ i hi f := by
    obtain ⟨h, H⟩ := Module.Baer.extension_property h i hi f
    exact ⟨h, DFunLike.congr_fun H⟩
/-
**Module.Baer.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] [Small.{v, u} R],   Module.Injective R Q → Module.Baer 
R Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Injective.out`：∀ {R : Type u} {inst : Ring R} {Q : Type v} {inst_
1 : AddCommGroup Q} {inst_2 : _root_.Module R Q}   [self : Module.Injective R Q]
 ⦃X Y : Ty…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Shrink.linearEquiv_symm_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : S
mall.{v, u_2} α] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α]   [inst_3 : _r
oot_.Module R α] (a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Shrink.linearEquiv_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : Small.
{v, u_2} α] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α]   [inst_3 : _root_.
Module R α] (a…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
protected theorem of_injective [Small.{v} R] (inj : Module.Injective R Q) : Module.Baer R Q := by
  intro I g
  let eI := Shrink.linearEquiv R I
  let eR := Shrink.linearEquiv R R
  obtain ⟨g', hg'⟩ := Module.Injective.out (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
    (eR.symm.injective.comp <| Subtype.val_injective.comp eI.injective) (g ∘ₗ eI.toLinearMap)
  exact ⟨g' ∘ₗ eR.symm.toLinearMap, fun x mx ↦ by simpa [eI, eR] using hg' (equivShrink I ⟨x, mx⟩)⟩
/-
**Module.Baer.iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Baer`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst_1 : AddCommGroup Q] [ins
t_2 : _root_.Module R Q] [Small.{v, u} R],   Module.Baer R Q ↔ Module.Injective 
R Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst
_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q],   Module.Baer R Q → Module.In
jective R Q
· 使用定理 `Module.Baer.of_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [i
nst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module.
Injective R Q …
-/
protected theorem iff_injective [Small.{v} R] : Module.Baer R Q ↔ Module.Injective R Q :=
  ⟨Module.Baer.injective, Module.Baer.of_injective⟩

end Module.Baer

section ULift

variable {M : Type v} [AddCommGroup M] [Module R M]

/-
**Module.ulift_injective_of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.ulift_injective_of_injective [Small.{v} R] (inj : Module.Injective 
R M) : Module.Injective R (ULift.{v'} M)
参数：inj : Module.Injective R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst
_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q],   Module.Baer R Q → Module.In
jective R Q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Baer.iff_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [
inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module
.Baer R Q ↔ Mod…
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
-/
lemma Module.ulift_injective_of_injective [Small.{v} R]
    (inj : Module.Injective R M) :
    Module.Injective R (ULift.{v'} M) := Module.Baer.injective fun I g ↦
  have ⟨g', hg'⟩ := Module.Baer.iff_injective.mpr inj I (ULift.moduleEquiv.toLinearMap ∘ₗ g)
  ⟨ULift.moduleEquiv.symm.toLinearMap ∘ₗ g', fun r hr ↦ ULift.ext _ _ <| hg' r hr⟩
/-
**Module.injective_of_ulift_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.injective_of_ulift_injective (inj : Module.Injective R (ULift.{v'} 
M)) : Module.Injective R M where out X Y _ _ _ _ f hf g
参数：inj : Module.Injective R (ULift.{v'} M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Injective.out`：∀ {R : Type u} {inst : Ring R} {Q : Type v} {inst_
1 : AddCommGroup Q} {inst_2 : _root_.Module R Q}   [self : Module.Injective R Q]
 ⦃X Y : Ty…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Module.injective_of_ulift_injective
    (inj : Module.Injective R (ULift.{v'} M)) :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let eX := ULift.moduleEquiv.{_, _, v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_, _, v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.moduleEquiv.symm.injective.comp <| hf.comp eX.injective)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMap)
    ⟨ULift.moduleEquiv.toLinearMap ∘ₗ g' ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
      fun x ↦ by exact congr(ULift.down $(hg' ⟨x⟩))⟩

variable (M) [Small.{v} R]
/-
**Module.injective_iff_ulift_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.injective_iff_ulift_injective : Module.Injective R M ↔ Module.Injec
tive R (ULift.{v'} M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.ulift_injective_of_injective`：Module.ulift_injective_of_injective
 [Small.{v} R] (inj : Module.Injective R M) : Module.Injective R (ULift.{v'} M)
· 使用引理 `Module.injective_of_ulift_injective`：Module.injective_of_ulift_injective
 (inj : Module.Injective R (ULift.{v'} M)) : Module.Injective R M where out X Y 
_ _ _ _ f hf g
-/
lemma Module.injective_iff_ulift_injective :
    Module.Injective R M ↔ Module.Injective R (ULift.{v'} M) :=
  ⟨Module.ulift_injective_of_injective R,
   Module.injective_of_ulift_injective R⟩

end ULift

section lifting_property

universe uR uM uP uP'

variable (R : Type uR) [Ring R] [Small.{uM} R]
variable (M : Type uM) [AddCommGroup M] [Module R M] [inj : Module.Injective R M]
variable (P : Type uP) [AddCommGroup P] [Module R P]
variable (P' : Type uP') [AddCommGroup P'] [Module R P']

/-
**Module.Injective.extension_property** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Injective.extension_property (f : P ->ₗ[R] P') (hf : Function.Injec
tive f) (g : P ->ₗ[R] M) : exists h : P' ->ₗ[R] M, h ∘ₗ f = g
参数：f : P ->ₗ[R] P'；hf : Function.Injective f；g : P ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.extension_property`：∀ {R : Type u} [inst : Ring R] {Q : Type
 v} [inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] {M : Type u_1}   {N :
 Type u_2} [inst_3 :…
· 使用定理 `Module.Baer.of_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [i
nst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module.
Injective R Q …
-/
lemma Module.Injective.extension_property
    (f : P →ₗ[R] P') (hf : Function.Injective f)
    (g : P →ₗ[R] M) : ∃ h : P' →ₗ[R] M, h ∘ₗ f = g :=
  (Module.Baer.of_injective inj).extension_property f hf g

end lifting_property


universe w in
/-
**Module.Injective.pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Injective.pi (R : Type u) [Ring R] {ι : Type w} (M : ι -> Type v) [
Small.{v} R] [forall i, AddCommGroup (M i)] [forall i, Module R (M i)] [forall i
, Module.Injective R (M i)] : Module.Injective R (forall i, M i)
参数：R : Type u；M : ι -> Type v；M i；M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `Module.Injective.extension_property`：Module.Injective.extension_property
 (f : P ->ₗ[R] P') (hf : Function.Injective f) (g : P ->ₗ[R] M) : exists h : P' 
->ₗ[R] M, h ∘ₗ f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance Module.Injective.pi
    (R : Type u) [Ring R] {ι : Type w} (M : ι → Type v) [Small.{v} R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] :
    Module.Injective R (∀ i, M i) :=
  ⟨fun X Y _ _ _ _ f hf g ↦ by
    choose l hl using fun i ↦ extension_property R _ _ _ f hf ((LinearMap.proj i).comp g)
    refine ⟨LinearMap.pi l, fun x ↦ ?_⟩
    ext i
    exact DFunLike.congr_fun (hl i) x⟩

set_option backward.isDefEq.respectTransparency false in
universe u' in
attribute [local instance] RingHomInvPair.of_ringEquiv in
/-
**Module.Injective.of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Injective.of_ringEquiv {R : Type u} [Ring R] [Small.{v} R] {S : Typ
e u'} [Ring S] {M : Type v} {N : Type v'} [AddCommGroup M] [AddCommGroup N] [Mod
ule R M] [Module S N] (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N) [
inj : Module.Injective R M] : Module.Injective S N
参数：e₁ : R ≃+* S；e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `Module.Baer.injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst
_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q],   Module.Baer R Q → Module.In
jective R Q
· 使用定理 `RingHomSurjective.instToRingHomRingEquiv`：∀ {R₁ : Type u_1} {R₂ : Type u
_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] (σ : R₁ ≃+* R₂), RingHomSurjecti
ve ↑σ
· 使用定理 `RingHomInvPair.symm`：symm (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHom
InvPair σ₁₂ σ₂₁] : RingHomInvPair σ₂₁ σ₁₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Module.Baer.of_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [i
nst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module.
Injective R Q …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.toSemilinearEquiv_symm_apply`：∀ {R : Type u_1} {S : Type u_6} 
[inst : Semiring R] [inst_1 : Semiring S] (f : R ≃+* S) (a : S),   f.toSemilinea
rEquiv.symm a = f.invFun a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Module.Injective.of_ringEquiv {R : Type u} [Ring R] [Small.{v} R] {S : Type u'} [Ring S]
    {M : Type v} {N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N)
    [inj : Module.Injective R M] : Module.Injective S N := by
  apply Module.Baer.injective (fun I g ↦ ?_)
  let I' := Submodule.map e₁.symm.toSemilinearEquiv.toLinearMap I
  let e : I' ≃ₛₗ[RingHomClass.toRingHom e₁] I := (e₁.symm.toSemilinearEquiv.submoduleMap I).symm
  let f : I' →ₗ[R] M := e₂.symm.toLinearMap.comp (g.comp e.toLinearMap)
  have hf (x) (hx : x ∈ I') : f ⟨x, hx⟩ = e₂.symm (g ⟨e₁ x, by simp_all [I']⟩) := rfl
  obtain ⟨f', hf'⟩ := Module.Baer.of_injective ‹_› I' f
  exact ⟨e₂.toLinearMap ∘ₛₗ f' ∘ₛₗ e₁.toSemilinearEquiv.symm.toLinearMap, by simp_all [I']⟩

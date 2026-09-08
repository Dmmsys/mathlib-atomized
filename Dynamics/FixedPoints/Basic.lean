/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.FixedPoints.Defs

/-!
# Fixed points of a self-map

We prove some simple lemmas about `IsFixedPt` and `∘`, `iterate`, and `Semiconj`.

## Tags

fixed point
-/

public section

open Equiv

universe u v

variable {α β : Type*} {f fa g : α → α} {x : α} {fb : β → β} {e : Perm α}

namespace Function

open Function (Commute)

namespace IsFixedPt

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
/-
**Function.IsFixedPt.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {f g : α → α} {x : α}, Function.IsFixedPt f x → Function.
IsFixedPt g x → Function.IsFixedPt (f ∘ g) x
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`.
-/
protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
  calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
/-
**Function.IsFixedPt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α}, Function.IsFixedPt f x → ∀ (n : ℕ), 
Function.IsFixedPt f^[n] x
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x

--- 原说明 ---
If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`.
-/
protected theorem iterate (hf : IsFixedPt f x) (n : ℕ) : IsFixedPt f^[n] x :=
  iterate_fixed hf n

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
/-
**Function.IsFixedPt.left_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`
。
形式化陈述：left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt 
f x
参数：hfg : IsFixedPt (f ∘ g) x；hg : IsFixedPt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`.
-/
theorem left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt f x :=
  calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
/-
**Function.IsFixedPt.to_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedP
t`。
形式化陈述：to_leftInverse (hf : IsFixedPt f x) (h : LeftInverse g f) : IsFixedPt g x
参数：hf : IsFixedPt f x；h : LeftInverse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a f
ixed
point of `g`.
-/
theorem to_leftInverse (hf : IsFixedPt f x) (h : LeftInverse g f) : IsFixedPt g x :=
  calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
/-
**Function.IsFixedPt.map** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {x : α},   Funct
ion.IsFixedPt fa x → ∀ {g : α → β}, Function.Semiconj g fa fb → Function.IsFixed
Pt fb (g x)
参数：g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixe
d points
of `fb`.
-/
protected theorem map {x : α} (hx : IsFixedPt fa x) {g : α → β} (h : Semiconj g fa fb) :
    IsFixedPt fb (g x) :=
  calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx
/-
**Function.IsFixedPt.apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α}, Function.IsFixedPt f x → Function.Is
FixedPt f (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem apply {x : α} (hx : IsFixedPt f x) : IsFixedPt f (f x) := by convert! hx
/-
**Function.IsFixedPt.preimage_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixe
dPt`。
形式化陈述：preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : Nat) 
: IsFixedPt (Set.preimage f^[n]) s
参数：h : IsFixedPt (Set.preimage f) s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_iterate_eq`：preimage_iterate_eq {f : α -> α} {n : Nat} : Se
t.preimage f^[n] = (Set.preimage f)^[n]
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
-/
theorem preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : ℕ) :
    IsFixedPt (Set.preimage f^[n]) s := by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n
/-
**Function.IsFixedPt.image_iterate** 是 Mathlib 中的一个引理，位于命名空间 `Function.IsFixedPt
`。
形式化陈述：image_iterate {s : Set α} (h : IsFixedPt (Set.image f) s) (n : Nat) : IsFi
xedPt (Set.image f^[n]) s
参数：h : IsFixedPt (Set.image f) s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_iterate_eq`：image_iterate_eq {f : α -> α} {n : Nat} : image (f
^[n]) = (image f)^[n]
-/
lemma image_iterate {s : Set α} (h : IsFixedPt (Set.image f) s) (n : ℕ) :
    IsFixedPt (Set.image f^[n]) s :=
  Set.image_iterate_eq ▸ h.iterate n
/-
**Function.IsFixedPt.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}, Function.IsFixedPt (⇑e) x → F
unction.IsFixedPt (⇑(Equiv.symm e)) x
参数：⇑e；⇑(Equiv.symm e)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.to_leftInverse`：to_leftInverse (hf : IsFixedPt f x) (
h : LeftInverse g f) : IsFixedPt g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.leftInverse_symm`：leftInverse_symm (f : α ≃ β) : LeftInverse f.sym
m f
-/
protected theorem equiv_symm (h : IsFixedPt e x) : IsFixedPt e.symm x :=
  h.to_leftInverse e.leftInverse_symm

@[simp]
/-
**Function.IsFixedPt.equiv_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedP
t`。
形式化陈述：equiv_symm_iff : IsFixedPt e.symm x ↔ IsFixedPt e x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.IsFixedPt.equiv_symm`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm 
α}, Function.IsFixedPt (⇑e) x → Function.IsFixedPt (⇑(Equiv.symm e)) x
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
-/
theorem equiv_symm_iff : IsFixedPt e.symm x ↔ IsFixedPt e x :=
  ⟨fun h ↦ e.symm_symm ▸ h.equiv_symm, .equiv_symm⟩
/-
**Function.IsFixedPt.perm_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}, Function.IsFixedPt (⇑e) x → F
unction.IsFixedPt (⇑e⁻¹) x
参数：⇑e；⇑e⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.equiv_symm`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm 
α}, Function.IsFixedPt (⇑e) x → Function.IsFixedPt (⇑(Equiv.symm e)) x
-/
protected theorem perm_inv (h : IsFixedPt e x) : IsFixedPt (⇑e⁻¹) x :=
  h.equiv_symm
/-
**Function.IsFixedPt.perm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}, Function.IsFixedPt (⇑e) x → ∀
 (n : ℕ), Function.IsFixedPt (⇑(e ^ n)) x
参数：⇑e；n : ℕ；⇑(e ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
-/
protected theorem perm_pow (h : IsFixedPt e x) (n : ℕ) : IsFixedPt (⇑(e ^ n)) x := h.iterate _
/-
**Function.IsFixedPt.perm_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}, Function.IsFixedPt (⇑e) x → ∀
 (n : ℤ), Function.IsFixedPt (⇑(e ^ n)) x
参数：⇑e；n : ℤ；⇑(e ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.perm_pow`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}
, Function.IsFixedPt (⇑e) x → ∀ (n : ℕ), Function.IsFixedPt (⇑(e ^ n)) x
· 使用定理 `Function.IsFixedPt.perm_inv`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}
, Function.IsFixedPt (⇑e) x → Function.IsFixedPt (⇑e⁻¹) x
-/
protected theorem perm_zpow (h : IsFixedPt e x) : ∀ n : ℤ, IsFixedPt (⇑(e ^ n)) x
  | Int.ofNat _ => h.perm_pow _
  | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv

end IsFixedPt

@[simp]
/-
**Function.fixedPoints_symm** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fixedPoints_symm : fixedPoints e.symm = fixedPoints e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fixedPoints_symm : fixedPoints e.symm = fixedPoints e := by
  simp [Set.ext_iff]

@[simp]
/-
**Function.Injective.isFixedPt_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inj
ective`。
形式化陈述：∀ {α : Type u_1} {f : α → α}, Function.Injective f → ∀ {x : α}, Function.I
sFixedPt f (f x) ↔ Function.IsFixedPt f x
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Function.IsFixedPt.apply`：∀ {α : Type u_1} {f : α → α} {x : α}, Function
.IsFixedPt f x → Function.IsFixedPt f (f x)
-/
theorem Injective.isFixedPt_apply_iff (hf : Injective f) {x : α} :
    IsFixedPt f (f x) ↔ IsFixedPt f x :=
  ⟨fun h => hf h.eq, IsFixedPt.apply⟩

/-- If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
/-
**Function.Semiconj.mapsTo_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semic
onj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {g : α → β},   F
unction.Semiconj g fa fb → Set.MapsTo g (Function.fixedPoints fa) (Function.fixe
dPoints fb)
参数：Function.fixedPoints fa；Function.fixedPoints fb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.map`：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb
 : β → β} {x : α},   Function.IsFixedPt fa x → ∀ {g : α → β}, Function.Semiconj 
g fa fb → Fu…

--- 原说明 ---
If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed 
points
of `fb`.
-/
theorem Semiconj.mapsTo_fixedPoints {g : α → β} (h : Semiconj g fa fb) :
    Set.MapsTo g (fixedPoints fa) (fixedPoints fb) := fun _ hx => hx.map h

/-- Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets of fixed points
of `f ∘ g` and `g ∘ f`, respectively. -/
/-
**Function.invOn_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invOn_fixedPoints_comp (f : α -> β) (g : β -> α) : Set.InvOn f g (fixedPoi
nts <| f ∘ g) (fixedPoints <| g ∘ f)
参数：f : α -> β；g : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets o
f fixed points
of `f ∘ g` and `g ∘ f`, respectively.
-/
theorem invOn_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  ⟨fun _ => id, fun _ => id⟩

/-- Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`. -/
/-
**Function.mapsTo_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mapsTo_fixedPoints_comp (f : α -> β) (g : β -> α) : Set.MapsTo f (fixedPoi
nts <| g ∘ f) (fixedPoints <| f ∘ g)
参数：f : α -> β；g : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.map`：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb
 : β → β} {x : α},   Function.IsFixedPt fa x → ∀ {g : α → β}, Function.Semiconj 
g fa fb → Fu…

--- 原说明 ---
Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`.
-/
theorem mapsTo_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.MapsTo f (fixedPoints <| g ∘ f) (fixedPoints <| f ∘ g) := fun _ hx => hx.map fun _ => rfl

/-- Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the fixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `invOn_fixedPoints_comp`. -/
/-
**Function.bijOn_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bijOn_fixedPoints_comp (f : α -> β) (g : β -> α) : Set.BijOn g (fixedPoint
s <| f ∘ g) (fixedPoints <| g ∘ f)
参数：f : α -> β；g : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `Function.invOn_fixedPoints_comp`：invOn_fixedPoints_comp (f : α -> β) (g 
: β -> α) : Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f)
· 使用定理 `Function.mapsTo_fixedPoints_comp`：mapsTo_fixedPoints_comp (f : α -> β) (
g : β -> α) : Set.MapsTo f (fixedPoints <| g ∘ f) (fixedPoints <| f ∘ g)

--- 原说明 ---
Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the f
ixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `invOn_f
ixedPoints_comp`.
-/
theorem bijOn_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  (invOn_fixedPoints_comp f g).bijOn (mapsTo_fixedPoints_comp g f) (mapsTo_fixedPoints_comp f g)

/-- If self-maps `f` and `g` commute, then they are inverse of each other on the set of fixed points
of `f ∘ g`. This is a particular case of `Function.invOn_fixedPoints_comp`. -/
/-
**Function.Commute.invOn_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Co
mmute`。
形式化陈述：∀ {α : Type u_1} {f g : α → α},   Function.Commute f g → Set.InvOn f g (Fu
nction.fixedPoints (f ∘ g)) (Function.fixedPoints (f ∘ g))
参数：Function.fixedPoints (f ∘ g)；Function.fixedPoints (f ∘ g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.invOn_fixedPoints_comp`：invOn_fixedPoints_comp (f : α -> β) (g 
: β -> α) : Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f)

--- 原说明 ---
If self-maps `f` and `g` commute, then they are inverse of each other on the set
 of fixed points
of `f ∘ g`. This is a particular case of `Function.invOn_fixedPoints_comp`.
-/
theorem Commute.invOn_fixedPoints_comp (h : Commute f g) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using Function.invOn_fixedPoints_comp f g

/-- If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `Function.bijOn_fixedPoints_comp`. -/
/-
**Function.Commute.left_bijOn_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Commute`。
形式化陈述：∀ {α : Type u_1} {f g : α → α},   Function.Commute f g → Set.BijOn f (Func
tion.fixedPoints (f ∘ g)) (Function.fixedPoints (f ∘ g))
参数：Function.fixedPoints (f ∘ g)；Function.fixedPoints (f ∘ g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
· 使用定理 `Function.bijOn_fixedPoints_comp`：bijOn_fixedPoints_comp (f : α -> β) (g 
: β -> α) : Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f)

--- 原说明 ---
If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed poin
ts of `f ∘ g`.
This is a particular case of `Function.bijOn_fixedPoints_comp`.
-/
theorem Commute.left_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn f (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp g f

/-- If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `Function.bijOn_fixedPoints_comp`. -/
/-
**Function.Commute.right_bijOn_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.Commute`。
形式化陈述：∀ {α : Type u_1} {f g : α → α},   Function.Commute f g → Set.BijOn g (Func
tion.fixedPoints (f ∘ g)) (Function.fixedPoints (f ∘ g))
参数：Function.fixedPoints (f ∘ g)；Function.fixedPoints (f ∘ g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.bijOn_fixedPoints_comp`：bijOn_fixedPoints_comp (f : α -> β) (g 
: β -> α) : Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f)

--- 原说明 ---
If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed poin
ts of `f ∘ g`.
This is a particular case of `Function.bijOn_fixedPoints_comp`.
-/
theorem Commute.right_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp f g

end Function


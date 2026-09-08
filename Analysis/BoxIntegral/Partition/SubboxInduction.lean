/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.SubboxInduction
public import Mathlib.Analysis.BoxIntegral.Partition.Tagged

/-!
# Induction on subboxes

In this file we prove (see
`BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic`) that for every box `I`
in `ℝⁿ` and a function `r : ℝⁿ → ℝ` positive on `I` there exists a tagged partition `π` of `I` such
that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

Later we will use this lemma to prove that the Henstock filter is nontrivial, hence the Henstock
integral is well-defined.

## Tags

partition, tagged partition, Henstock integral
-/

@[expose] public section


namespace BoxIntegral

open Set Metric

open Topology

noncomputable section

variable {ι : Type*} [Fintype ι] {I J : Box ι}

namespace Prepartition

/-- Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center. -/
/-
**BoxIntegral.Prepartition.splitCenter** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：splitCenter (I : Box ι) : Prepartition I where boxes
参数：I : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center
.
-/
def splitCenter (I : Box ι) : Prepartition I where
  boxes := Finset.univ.map (Box.splitCenterBoxEmb I)
  le_of_mem' := by simp [I.splitCenterBox_le]
  pairwiseDisjoint := by
    rw [Finset.coe_map, Finset.coe_univ, image_univ]
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne
    exact I.disjoint_splitCenterBox (mt (congr_arg _) Hne)

@[simp]
/-
**BoxIntegral.Prepartition.mem_splitCenter** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：mem_splitCenter : J in splitCenter I ↔ exists s, I.splitCenterBox s = J
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
· 使用定理 `BoxIntegral.Box.splitCenterBoxEmb_apply`：∀ {ι : Type u_1} (I : BoxIntegr
al.Box ι) (s : Set ι), I.splitCenterBoxEmb s = I.splitCenterBox s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_splitCenter : J ∈ splitCenter I ↔ ∃ s, I.splitCenterBox s = J := by simp [splitCenter]
/-
**BoxIntegral.Prepartition.isPartition_splitCenter** 是 Mathlib 中的一个定理，位于命名空间 `Bo
xIntegral.Prepartition`。
形式化陈述：isPartition_splitCenter (I : Box ι) : IsPartition (splitCenter I)
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem isPartition_splitCenter (I : Box ι) : IsPartition (splitCenter I) := fun x hx => by
  simp [hx]
/-
**BoxIntegral.Prepartition.upper_sub_lower_of_mem_splitCenter** 是 Mathlib 中的一个定理
，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：upper_sub_lower_of_mem_splitCenter (h : J in splitCenter I) (i : ι) : J.up
per i - J.lower i = (I.upper i - I.lower i) / 2
参数：h : J in splitCenter I；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_splitCenter`：mem_splitCenter : J in splitCe
nter I ↔ exists s, I.splitCenterBox s = J
· 使用定理 `BoxIntegral.Box.upper_sub_lower_splitCenterBox`：upper_sub_lower_splitCen
terBox (I : Box ι) (s : Set ι) (i : ι) : (I.splitCenterBox s).upper i - (I.split
CenterBox s).lower i = (I.upper i - …
-/
theorem upper_sub_lower_of_mem_splitCenter (h : J ∈ splitCenter I) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
  let ⟨s, hs⟩ := mem_splitCenter.1 h
  hs ▸ I.upper_sub_lower_splitCenterBox s i

end Prepartition

namespace Box

open Prepartition TaggedPrepartition

/-- Let `p` be a predicate on `Box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `BoxIntegral.Box.subbox_induction_on'` for a version using
`BoxIntegral.Box.splitCenterBox` instead of `BoxIntegral.Prepartition.splitCenter`. -/
@[elab_as_elim]
/-
**BoxIntegral.Box.subbox_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box
`。
形式化陈述：subbox_induction_on {p : Box ι -> Prop} (I : Box ι) (H_ind : forall J <= I
, (forall J' in splitCenter J, p J') -> p J) (H_nhds : forall z in Box.Icc I, ex
ists U in 𝓝[Box.Icc I] z, forall J <= I, forall (m : Nat), z in Box.Icc J -> Box
.Icc J subseteq U -> (forall i, J.upper i - J.lower i = (I.upper i - I.lower i) 
/ 2 ^ m) -> p J) : p I
参数：I : Box ι；H_ind : forall J <= I, (forall J' in splitCenter J, p J') -> p J；H_
nhds : forall z in Box.Icc I, exists U in 𝓝[Box.Icc I] z, forall J <= I, forall 
(m : Nat), z in Box.Icc J -> Box.Icc J subseteq U -> (forall i, J.upper i - J.lo
wer i = (I.upper i - I.lower i) / 2 ^ m) -> p J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BoxIntegral.Box.subbox_induction_on'`：subbox_induction_on' {p : Box ι ->
 Prop} (I : Box ι) (H_ind : forall J <= I, (forall s, p (splitCenterBox J s)) ->
 p J) (H_nhds : forall z i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_splitCenter`：mem_splitCenter : J in splitCe
nter I ↔ exists s, I.splitCenterBox s = J

--- 原说明 ---
Let `p` be a predicate on `Box ι`, let `I` be a box. Suppose that the following 
two properties
hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of 
`J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` 
within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to 
`I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `BoxIntegral.Box.subbox_induction_on'` for a versio
n using
`BoxIntegral.Box.splitCenterBox` instead of `BoxIntegral.Prepartition.splitCente
r`.
-/
theorem subbox_induction_on {p : Box ι → Prop} (I : Box ι)
    (H_ind : ∀ J ≤ I, (∀ J' ∈ splitCenter J, p J') → p J)
    (H_nhds : ∀ z ∈ Box.Icc I, ∃ U ∈ 𝓝[Box.Icc I] z, ∀ J ≤ I, ∀ (m : ℕ),
      z ∈ Box.Icc J → Box.Icc J ⊆ U →
        (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
    p I := by
  refine subbox_induction_on' I (fun J hle hs => H_ind J hle fun J' h' => ?_) H_nhds
  rcases mem_splitCenter.1 h' with ⟨s, rfl⟩
  exact hs s

/-- Given a box `I` in `ℝⁿ` and a function `r : ℝⁿ → (0, ∞)`, there exists a tagged partition `π` of
`I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ m`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock integral is
well-defined. -/
/-
**BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic** 是
 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：exists_taggedPartition_isHenstock_isSubordinate_homothetic (I : Box ι) (r 
: (ι -> Real) -> Ioi (0 : Real)) : exists π : TaggedPrepartition I, π.IsPartitio
n ∧ π.IsHenstock ∧ π.IsSubordinate r ∧ (forall J in π, exists m : Nat, forall i,
 (J :).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) ∧ π.distortion = I
.distortion
参数：I : Box ι；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.subbox_induction_on`：subbox_induction_on {p : Box ι -> P
rop} (I : Box ι) (H_ind : forall J <= I, (forall J' in splitCenter J, p J') -> p
 J) (H_nhds : forall z in…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BoxIntegral.Prepartition.IsPartition.biUnionTagged`：∀ {ι : Type u_1} {I 
: BoxIntegral.Box ι} {π : BoxIntegral.Prepartition I},   π.IsPartition →     ∀ {
πi : (J : BoxIntegral.Box ι) → BoxIntegr…
· 使用定理 `BoxIntegral.Prepartition.isPartition_splitCenter`：isPartition_splitCente
r (I : Box ι) : IsPartition (splitCenter I)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_biUnionTagged`：mem_biUnionTagged (π : Prepa
rtition I) {πi : forall J, TaggedPrepartition J} : J in π.biUnionTagged πi ↔ exi
sts J' in π, J in πi J'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.upper_sub_lower_of_mem_splitCenter`：upper_sub_l
ower_of_mem_splitCenter (h : J in splitCenter I) (i : ι) : J.upper i - J.lower i
 = (I.upper i - I.lower i) / 2
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.TaggedPrepartition.isHenstock_biUnionTagged`：isHenstock_biUn
ionTagged {π : Prepartition I} {πi : forall J, TaggedPrepartition J} : IsHenstoc
k (π.biUnionTagged πi) ↔ forall J in π, (πi J…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTagged`：isSubordinat
e_biUnionTagged [Fintype ι] {π : Prepartition I} {πi : forall J, TaggedPrepartit
ion J} : IsSubordinate (π.biUnionTagged πi) r ↔ …
· 使用定理 `BoxIntegral.TaggedPrepartition.distortion_of_const`：distortion_of_const 
{c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.distortion J = c) : π.disto
rtion = c
· 使用定理 `BoxIntegral.Prepartition.IsPartition.nonempty_boxes`：nonempty_boxes (h :
 π.IsPartition) : π.boxes.Nonempty
· 使用定理 `BoxIntegral.Box.distortion_eq_of_sub_eq_div`：distortion_eq_of_sub_eq_div
 {I J : Box ι} {r : Real} (h : forall i, I.upper i - I.lower i = (J.upper i - J.
lower i) / r) : distortion I = di…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Given a box `I` in `ℝⁿ` and a function `r : ℝⁿ → (0, ∞)`, there exists a tagged 
partition `π` of
`I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ m`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock in
tegral is
well-defined.
-/
theorem exists_taggedPartition_isHenstock_isSubordinate_homothetic (I : Box ι)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π : TaggedPrepartition I, π.IsPartition ∧ π.IsHenstock ∧ π.IsSubordinate r ∧
      (∀ J ∈ π, ∃ m : ℕ, ∀ i, (J :).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) ∧
        π.distortion = I.distortion := by
  refine subbox_induction_on I (fun J _ hJ => ?_) fun z _ => ?_
  · choose! πi hP hHen hr Hn _ using hJ
    choose! n hn using Hn
    have hP : ((splitCenter J).biUnionTagged πi).IsPartition :=
      (isPartition_splitCenter _).biUnionTagged hP
    have hsub : ∀ J' ∈ (splitCenter J).biUnionTagged πi, ∃ n : ℕ, ∀ i,
        (J' :).upper i - J'.lower i = (J.upper i - J.lower i) / 2 ^ n := by
      intro J' hJ'
      rcases (splitCenter J).mem_biUnionTagged.1 hJ' with ⟨J₁, h₁, h₂⟩
      refine ⟨n J₁ J' + 1, fun i => ?_⟩
      simp only [hn J₁ h₁ J' h₂, upper_sub_lower_of_mem_splitCenter h₁, pow_succ', div_div]
    refine ⟨_, hP, isHenstock_biUnionTagged.2 hHen, isSubordinate_biUnionTagged.2 hr, hsub, ?_⟩
    refine TaggedPrepartition.distortion_of_const _ hP.nonempty_boxes fun J' h' => ?_
    rcases hsub J' h' with ⟨n, hn⟩
    exact Box.distortion_eq_of_sub_eq_div hn
  · refine ⟨Box.Icc I ∩ closedBall z (r z),
      inter_mem_nhdsWithin _ (closedBall_mem_nhds _ (r z).coe_prop), ?_⟩
    intro J _ n Hmem HIcc Hsub
    rw [Set.subset_inter_iff] at HIcc
    refine ⟨single _ _ le_rfl _ Hmem, isPartition_single _, isHenstock_single _,
      (isSubordinate_single _ _).2 HIcc.2, ?_, distortion_single _ _⟩
    simp only [TaggedPrepartition.mem_single, forall_eq]
    refine ⟨0, fun i => ?_⟩
    simp

end Box

namespace Prepartition

open TaggedPrepartition Finset Function

/-- Given a box `I` in `ℝⁿ`, a function `r : ℝⁿ → (0, ∞)`, and a prepartition `π` of `I`, there
exists a tagged prepartition `π'` of `I` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
/-
**BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq**
 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : TaggedPrepartition 
I, π'.toPrepartition <= π ∧ π'.IsHenstock ∧ π'.IsSubordinate r ∧ π'.distortion =
 π.distortion ∧ π'.iUnion = π.iUnion
参数：r : (ι -> Real) -> Ioi (0 : Real)；π : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothet
ic`：exists_taggedPartition_isHenstock_isSubordinate_homothetic (I : Box ι) (r : 
(ι -> Real) -> Ioi (0 : Real)) : exists π : TaggedPrepartition I…
· 使用定理 `BoxIntegral.Prepartition.biUnion_le`：biUnion_le (πi : forall J, Preparti
tion J) : π.biUnion πi <= π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.TaggedPrepartition.isHenstock_biUnionTagged`：isHenstock_biUn
ionTagged {π : Prepartition I} {πi : forall J, TaggedPrepartition J} : IsHenstoc
k (π.biUnionTagged πi) ↔ forall J in π, (πi J…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTagged`：isSubordinat
e_biUnionTagged [Fintype ι] {π : Prepartition I} {πi : forall J, TaggedPrepartit
ion J} : IsSubordinate (π.biUnionTagged πi) r ↔ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.distortion_biUnionTagged`：∀ {ι : Type u_1} {I :
 BoxIntegral.Box ι} [inst : Fintype ι] (π : BoxIntegral.Prepartition I)   (πi : 
(J : BoxIntegral.Box ι) → BoxIntegral.T…
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `BoxIntegral.Prepartition.iUnion_biUnion_partition`：iUnion_biUnion_partit
ion (h : forall J in π, (πi J).IsPartition) : (π.biUnion πi).iUnion = π.iUnion
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a box `I` in `ℝⁿ`, a function `r : ℝⁿ → (0, ∞)`, and a prepartition `π` of
 `I`, there
exists a tagged prepartition `π'` of `I` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
theorem exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : Prepartition I) :
    ∃ π' : TaggedPrepartition I, π'.toPrepartition ≤ π ∧ π'.IsHenstock ∧ π'.IsSubordinate r ∧
      π'.distortion = π.distortion ∧ π'.iUnion = π.iUnion := by
  have := fun J => Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic J r
  choose! πi πip πiH πir _ πid using this
  refine ⟨π.biUnionTagged πi, biUnion_le _ _, isHenstock_biUnionTagged.2 fun J _ => πiH J,
    isSubordinate_biUnionTagged.2 fun J _ => πir J, ?_, π.iUnion_biUnion_partition fun J _ => πip J⟩
  rw [distortion_biUnionTagged]
  exact sup_congr rfl fun J _ => πid J

/-- Given a prepartition `π` of a box `I` and a function `r : ℝⁿ → (0, ∞)`, `π.toSubordinate r`
is a tagged partition `π'` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
/-
**BoxIntegral.Prepartition.toSubordinate** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：toSubordinate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 : Real)) : T
aggedPrepartition I
参数：π : Prepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…

--- 原说明 ---
Given a prepartition `π` of a box `I` and a function `r : ℝⁿ → (0, ∞)`, `π.toSub
ordinate r`
is a tagged partition `π'` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
def toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose
/-
**BoxIntegral.Prepartition.toSubordinate_toPrepartition_le** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.Prepartition`。
形式化陈述：toSubordinate_toPrepartition_le (π : Prepartition I) (r : (ι -> Real) -> I
oi (0 : Real)) : (π.toSubordinate r).toPrepartition <= π
参数：π : Prepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem toSubordinate_toPrepartition_le (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).toPrepartition ≤ π :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.1
/-
**BoxIntegral.Prepartition.isHenstock_toSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.Prepartition`。
形式化陈述：isHenstock_toSubordinate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 :
 Real)) : (π.toSubordinate r).IsHenstock
参数：π : Prepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem isHenstock_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsHenstock :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.1
/-
**BoxIntegral.Prepartition.isSubordinate_toSubordinate** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.Prepartition`。
形式化陈述：isSubordinate_toSubordinate (π : Prepartition I) (r : (ι -> Real) -> Ioi (
0 : Real)) : (π.toSubordinate r).IsSubordinate r
参数：π : Prepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem isSubordinate_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsSubordinate r :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.1

@[simp]
/-
**BoxIntegral.Prepartition.distortion_toSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.Prepartition`。
形式化陈述：distortion_toSubordinate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 :
 Real)) : (π.toSubordinate r).distortion = π.distortion
参数：π : Prepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem distortion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).distortion = π.distortion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.1

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_toSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：iUnion_toSubordinate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 : Rea
l)) : (π.toSubordinate r).iUnion = π.iUnion
参数：π : Prepartition I；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem iUnion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).iUnion = π.iUnion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.2

end Prepartition

namespace TaggedPrepartition

/-- Given a tagged prepartition `π₁`, a prepartition `π₂` that covers exactly `I \ π₁.iUnion`, and
a function `r : ℝⁿ → (0, ∞)`, returns the union of `π₁` and `π₂.toSubordinate r`. This partition
`π` has the following properties:

* `π` is a partition, i.e. it covers the whole `I`;
* `π₁.boxes ⊆ π.boxes`;
* `π.tag J = π₁.tag J` whenever `J ∈ π₁`;
* `π` is Henstock outside of `π₁`: `π.tag J ∈ J.Icc` whenever `J ∈ π`, `J ∉ π₁`;
* `π` is subordinate to `r` outside of `π₁`;
* the distortion of `π` is equal to the maximum of the distortions of `π₁` and `π₂`.
-/
/-
**BoxIntegral.TaggedPrepartition.unionComplToSubordinate** 是 Mathlib 中的一个定义，位于命名
空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I) 
(hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> Ioi (0 : Real)) : TaggedPr
epartition I
参数：π₁ : TaggedPrepartition I；π₂ : Prepartition I；hU : π₂.iUnion = ↑I \ π₁.iUnion
；r : (ι -> Real) -> Ioi (0 : Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a tagged prepartition `π₁`, a prepartition `π₂` that covers exactly `I \ π
₁.iUnion`, and
a function `r : ℝⁿ → (0, ∞)`, returns the union of `π₁` and `π₂.toSubordinate r`
. This partition
`π` has the following properties:

* `π` is a partition, i.e. it covers the whole `I`;
* `π₁.boxes ⊆ π.boxes`;
* `π.tag J = π₁.tag J` whenever `J ∈ π₁`;
* `π` is Henstock outside of `π₁`: `π.tag J ∈ J.Icc` whenever `J ∈ π`, `J ∉ π₁`;
* `π` is subordinate to `r` outside of `π₁`;
* the distortion of `π` is equal to the maximum of the distortions of `π₁` and `
π₂`.
-/
def unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  π₁.disjUnion (π₂.toSubordinate r)
    (((π₂.iUnion_toSubordinate r).trans hU).symm ▸ disjoint_sdiff_self_right)
/-
**BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinate** 是 Mathlib
 中的一个定理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：isPartition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prep
artition I) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> Ioi (0 : Real)
) : IsPartition (π₁.unionComplToSubordinate π₂ hU r)
参数：π₁ : TaggedPrepartition I；π₂ : Prepartition I；hU : π₂.iUnion = ↑I \ π₁.iUnion
；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.isPartitionDisjUnionOfEqDiff`：isPartitionDisjUn
ionOfEqDiff (h : π₂.iUnion = ↑I \ π₁.iUnion) : IsPartition (π₁.disjUnion π₂ <| h
.symm ▸ disjoint_sdiff_self_right)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.iUnion_toSubordinate`：iUnion_toSubordinate (π :
 Prepartition I) (r : (ι -> Real) -> Ioi (0 : Real)) : (π.toSubordinate r).iUnio
n = π.iUnion
-/
theorem isPartition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    IsPartition (π₁.unionComplToSubordinate π₂ hU r) :=
  Prepartition.isPartitionDisjUnionOfEqDiff ((π₂.iUnion_toSubordinate r).trans hU)

open scoped Classical in
@[simp]
/-
**BoxIntegral.TaggedPrepartition.unionComplToSubordinate_boxes** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartiti
on I) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> Ioi (0 : Real)) : (π
₁.unionComplToSubordinate π₂ hU r).boxes = π₁.boxes union (π₂.toSubordinate r).b
oxes
参数：π₁ : TaggedPrepartition I；π₂ : Prepartition I；hU : π₂.iUnion = ↑I \ π₁.iUnion
；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).boxes = π₁.boxes ∪ (π₂.toSubordinate r).boxes := rfl

@[simp]
/-
**BoxIntegral.TaggedPrepartition.iUnion_unionComplToSubordinate_boxes** 是 Mathli
b 中的一个定理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：iUnion_unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Pre
partition I) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> Ioi (0 : Real
)) : (π₁.unionComplToSubordinate π₂ hU r).iUnion = I
参数：π₁ : TaggedPrepartition I；π₂ : Prepartition I；hU : π₂.iUnion = ↑I \ π₁.iUnion
；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
· 使用定理 `BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinate`：isPa
rtition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I
) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> …
-/
theorem iUnion_unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).iUnion = I :=
  (isPartition_unionComplToSubordinate _ _ _ _).iUnion_eq

@[simp]
/-
**BoxIntegral.TaggedPrepartition.distortion_unionComplToSubordinate** 是 Mathlib 
中的一个定理，位于命名空间 `BoxIntegral.TaggedPrepartition`。
形式化陈述：distortion_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepa
rtition I) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> Ioi (0 : Real))
 : (π₁.unionComplToSubordinate π₂ hU r).distortion = max π₁.distortion π₂.distor
tion
参数：π₁ : TaggedPrepartition I；π₂ : Prepartition I；hU : π₂.iUnion = ↑I \ π₁.iUnion
；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.TaggedPrepartition.distortion_disjUnion`：distortion_disjUnio
n (h : Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).distortion = max π₁.d
istortion π₂.distortion
· 使用定理 `BoxIntegral.Prepartition.distortion_toSubordinate`：distortion_toSubordin
ate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 : Real)) : (π.toSubordinate 
r).distortion = π.distortion
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem distortion_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).distortion = max π₁.distortion π₂.distortion := by
  simp [unionComplToSubordinate]

end TaggedPrepartition

end

end BoxIntegral


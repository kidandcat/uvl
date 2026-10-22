import UVL.Render.Damage

/-!
# Pixels outside a damage window

`Frame.update` repaints a frame by blitting `Raster.renderWindow` into the
previous pixels. This file proves the blit, and therefore the update, leaves
every byte outside those windows unchanged. There is no `sorry` and no axiom.

`Tile.renderTiled` is a different statement: each tile is rasterized on its
own and then blitted, and the tests check that the assembly matches
`Raster.render` bit for bit. Proving that equality needs a semantics of the
scanline rasterizer (coverage, clips, and which ops `TileList.select` keeps).
The blit theorem is what partial redraw uses; the rasterizer equality is left
to those tests.
-/

namespace UVL

namespace Window

/-- Byte `i` of a `w`-wide RGBA image does not belong to `win`. -/
def missesByte (win : Window) (w i : Nat) : Prop :=
  w = 0 ∨ i / 4 % w < win.x ∨ win.x + win.w ≤ i / 4 % w ∨
    i / 4 / w < win.y ∨ win.y + win.h ≤ i / 4 / w

/-- The full frame window covers every byte of a `w × h` RGBA buffer. -/
theorem full_not_miss (w h i : Nat) (hi : i < w * h * 4) :
    ¬ missesByte ⟨0, 0, w, h⟩ w i := by
  intro hm
  dsimp [missesByte] at hm
  simp only [Nat.zero_add] at hm
  have hw : 0 < w := by
    cases w with
    | zero => simp at hi
    | succ _ => exact Nat.succ_pos _
  have hh : 0 < h := by
    cases h with
    | zero => simp [Nat.mul_zero] at hi
    | succ _ => exact Nat.succ_pos _
  rcases hm with hw0 | hxl | hxg | hyl | hyg
  · exact absurd hw0 (Nat.ne_of_gt hw)
  · exact Nat.not_lt_zero _ hxl
  · exact Nat.not_le_of_gt (Nat.mod_lt (i / 4) hw) hxg
  · exact Nat.not_lt_zero _ hyl
  · have hp : i / 4 < w * h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr hi
    have hy : i / 4 / w < h :=
      (Nat.div_lt_iff_lt_mul hw).mpr (by simpa [Nat.mul_comm] using hp)
    exact Nat.not_le_of_gt hy hyg

end Window

private theorem copySlice_size (src dest : ByteArray) (srcOff destOff len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : destOff + len ≤ dest.size) :
    (src.copySlice srcOff dest destOff len).size = dest.size := by
  rw [ByteArray.copySlice_eq_append]
  have hmin : min len (src.data.size - srcOff) = len := by
    rw [ByteArray.size_data]; omega
  rw [hmin, ByteArray.size_data]
  simp only [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero]
  have h1 : min destOff dest.size = destOff := Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) hdest)
  have h2 : min (srcOff + len) src.size = srcOff + len := Nat.min_eq_left hsrc
  have h3 : min dest.size dest.size = dest.size := Nat.min_self _
  rw [h1, h2, h3]
  omega

/-- Model of `copySlice` once the source slice is long enough to fill `len`. -/
private def copied (src dest : ByteArray) (srcOff destOff len : Nat) : ByteArray :=
  dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
    dest.extract (destOff + len) dest.size

private theorem copySlice_eq_copied (src dest : ByteArray) (srcOff destOff len : Nat)
    (hsrc : srcOff + len ≤ src.size) :
    src.copySlice srcOff dest destOff len = copied src dest srcOff destOff len := by
  unfold copied
  rw [ByteArray.copySlice_eq_append]
  have hmin : min len (src.data.size - srcOff) = len := by
    rw [ByteArray.size_data]; omega
  rw [hmin, ByteArray.size_data]

private theorem getElem!_append_left (a b : ByteArray) (i : Nat) (hi : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  have h : i < (a ++ b).size := by simp; omega
  rw [getElem!_pos (a ++ b) i h, getElem!_pos a i hi]
  exact ByteArray.getElem_append_left (h := h) hi

private theorem getElem!_append_right (a b : ByteArray) (i : Nat)
    (hle : a.size ≤ i) (hi : i < (a ++ b).size) :
    (a ++ b)[i]! = b[i - a.size]! := by
  have hb : i - a.size < b.size := by simp at hi; omega
  rw [getElem!_pos (a ++ b) i hi, getElem!_pos b (i - a.size) hb]
  exact ByteArray.getElem_append_right (h := hi) hle

private theorem getElem!_extract (b : ByteArray) (start stop i : Nat)
    (hi : i < (b.extract start stop).size) :
    (b.extract start stop)[i]! = b[start + i]! := by
  rw [getElem!_pos (b.extract start stop) i hi,
      getElem!_pos b (start + i) (ByteArray.getElem_extract_aux hi)]
  exact ByteArray.getElem_extract hi

private theorem copied_get (src dest : ByteArray) (srcOff destOff len i : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : destOff + len ≤ dest.size)
    (hi : i < dest.size) (hout : i < destOff ∨ destOff + len ≤ i) :
    (copied src dest srcOff destOff len)[i]! = dest[i]! := by
  have hL : (dest.extract 0 destOff).size = destOff := by
    simp [ByteArray.size_extract]; omega
  have hM : (src.extract srcOff (srcOff + len)).size = len := by
    simp [ByteArray.size_extract]; omega
  have hR : (dest.extract (destOff + len) dest.size).size = dest.size - (destOff + len) := by
    simp [ByteArray.size_extract]
  unfold copied
  rw [ByteArray.append_assoc]
  rcases hout with hlt | hge
  · rw [getElem!_append_left _ _ _ (by simpa [hL] using hlt)]
    rw [getElem!_extract _ _ _ _ (by simpa [hL] using hlt)]
    simp
  · have hi' : i < (dest.extract 0 destOff ++
        (src.extract srcOff (srcOff + len) ++ dest.extract (destOff + len) dest.size)).size := by
      simp only [ByteArray.size_append, hL, hM, hR]
      omega
    rw [getElem!_append_right _ _ _ (by rw [hL]; omega) hi']
    have hi2 : i - (dest.extract 0 destOff).size <
        (src.extract srcOff (srcOff + len) ++ dest.extract (destOff + len) dest.size).size := by
      simp only [ByteArray.size_append, hL, hM, hR] at hi' ⊢
      omega
    rw [getElem!_append_right _ _ _ (by rw [hL, hM]; omega) hi2]
    rw [getElem!_extract _ _ _ _ (by
      simp only [ByteArray.size_extract, hL, hM]
      omega)]
    simp only [hL, hM]
    have hidx : destOff + len + (i - destOff - len) = i := by omega
    rw [hidx]

private theorem copySlice_get (src dest : ByteArray) (srcOff destOff len i : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : destOff + len ≤ dest.size)
    (hi : i < dest.size) (hout : i < destOff ∨ destOff + len ≤ i) :
    (src.copySlice srcOff dest destOff len)[i]! = dest[i]! := by
  rw [copySlice_eq_copied src dest srcOff destOff len hsrc]
  exact copied_get src dest srcOff destOff len i hsrc hdest hi hout

private theorem rowBytes_le (cw ch row : Nat) (hrow : row < ch) :
    row * cw * 4 + cw * 4 ≤ cw * ch * 4 := by
  have hstep : row * cw * 4 + cw * 4 = (row + 1) * cw * 4 := by
    calc row * cw * 4 + cw * 4
        = (row * cw + cw) * 4 := by rw [Nat.add_mul]
      _ = ((row + 1) * cw) * 4 := by rw [← Nat.succ_mul]
      _ = (row + 1) * cw * 4 := by rw [Nat.mul_assoc]
  have hmul : (row + 1) * cw * 4 ≤ ch * cw * 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hrow))
  have hcomm : ch * cw * 4 = cw * ch * 4 := by
    apply congrArg (· * 4)
    exact Nat.mul_comm ch cw
  omega

private theorem rowOff_le (w h tx ty cw row : Nat)
    (hx : tx + cw ≤ w) (hy : ty + row < h) :
    ((ty + row) * w + tx) * 4 + cw * 4 ≤ w * h * 4 := by
  have hspan : (ty + row) * w + tx + cw ≤ (ty + row + 1) * w := by
    have hsum : (ty + row) * w + (tx + cw) ≤ (ty + row) * w + w := Nat.add_le_add_left hx _
    have hre : (ty + row) * w + tx + cw = (ty + row) * w + (tx + cw) := by omega
    have hs : (ty + row) * w + w = (ty + row + 1) * w := by rw [← Nat.succ_mul]
    omega
  have hend : (ty + row + 1) * w ≤ h * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hy)
  have h4 : ((ty + row) * w + tx + cw) * 4 ≤ (h * w) * 4 :=
    Nat.mul_le_mul_right 4 (Nat.le_trans hspan hend)
  have hsplit : ((ty + row) * w + tx) * 4 + cw * 4 = ((ty + row) * w + tx + cw) * 4 := by
    rw [← Nat.right_distrib]
  have hframe : (h * w) * 4 = w * h * 4 := by
    rw [Nat.mul_comm h w]
  omega

/-- A byte that misses `⟨tx, ty, cw, ch⟩` misses row `row` of that window. -/
private theorem miss_outside_row (w tx ty cw ch row i : Nat)
    (hw : 0 < w) (hx : tx + cw ≤ w) (hrow : row < ch)
    (hm : Window.missesByte ⟨tx, ty, cw, ch⟩ w i) :
    i < ((ty + row) * w + tx) * 4 ∨
      ((ty + row) * w + tx) * 4 + cw * 4 ≤ i := by
  dsimp [Window.missesByte] at hm
  generalize hpdef : i / 4 = p at hm ⊢
  generalize hxdef : p % w = x at hm ⊢
  generalize hydef : p / w = y at hm ⊢
  have hmod : x < w := by simpa [hxdef] using Nat.mod_lt p hw
  have hp : y * w + x = p := by
    simpa [hxdef, hydef, Nat.mul_comm] using Nat.div_add_mod p w
  let lo := (ty + row) * w + tx
  suffices p < lo ∨ lo + cw ≤ p by
    rcases this with h | h
    · left
      have : i < lo * 4 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp (by simpa [hpdef] using h)
      simpa [lo] using this
    · right
      have h4 : (lo + cw) * 4 ≤ i :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mp (by simpa [hpdef] using h)
      have heq : (lo + cw) * 4 = lo * 4 + cw * 4 := by
        rw [Nat.mul_comm, Nat.mul_add, Nat.mul_comm 4 lo, Nat.mul_comm 4 cw]
      simpa [heq, lo] using h4
  have low (hlt : y < ty + row) : p < lo := by
    have hxlt : y * w + x < y * w + w := Nat.add_lt_add_left hmod _
    have hyw : y * w + w = (y + 1) * w := by rw [Nat.succ_mul]
    have hle : (y + 1) * w ≤ (ty + row) * w := Nat.mul_le_mul_right w hlt
    have : y * w + x < (ty + row) * w := Nat.lt_of_lt_of_le (by rwa [hyw] at hxlt) hle
    have hlo : (ty + row) * w ≤ lo := Nat.le_add_right _ tx
    rw [← hp]
    exact Nat.lt_of_lt_of_le this hlo
  have high (hgt : ty + row < y) : lo + cw ≤ p := by
    have hmul : (ty + row + 1) * w ≤ y * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hgt)
    have hsum : (ty + row) * w + w = (ty + row + 1) * w := by rw [Nat.succ_mul]
    have hleft : lo + cw ≤ (ty + row) * w + w := by
      have hsum' : (ty + row) * w + (tx + cw) ≤ (ty + row) * w + w := Nat.add_le_add_left hx _
      have hre : lo + cw = (ty + row) * w + (tx + cw) := by
        show (ty + row) * w + tx + cw = (ty + row) * w + (tx + cw)
        omega
      omega
    have : lo + cw ≤ y * w := Nat.le_trans hleft (hsum.symm ▸ hmul)
    rw [← hp]
    exact Nat.le_trans this (Nat.le_add_right _ x)
  rcases hm with hw0 | hxl | hxg | hyl | hyg
  · exact absurd hw0 (Nat.ne_of_gt hw)
  · by_cases hylt : y < ty + row
    · exact Or.inl (low hylt)
    · by_cases heq : y = ty + row
      · left
        rw [← hp, heq]
        exact Nat.add_lt_add_left hxl _
      · right
        exact high (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hylt) (Ne.symm heq))
  · by_cases hylt : y < ty + row
    · exact Or.inl (low hylt)
    · by_cases heq : y = ty + row
      · right
        rw [← hp, heq]
        have hsum' : (ty + row) * w + (tx + cw) ≤ (ty + row) * w + x :=
          Nat.add_le_add_left hxg _
        have hre : lo + cw = (ty + row) * w + (tx + cw) := by
          show (ty + row) * w + tx + cw = (ty + row) * w + (tx + cw)
          omega
        omega
      · right
        exact high (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hylt) (Ne.symm heq))
  · exact Or.inl (low (Nat.lt_of_lt_of_le hyl (Nat.le_add_right _ _)))
  · exact Or.inr (high (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrow ty) hyg))

private def paintRows (w cw ty tx : Nat) (tile dst : ByteArray) (n : Nat) : ByteArray :=
  (List.range n).foldl (fun dst row =>
    tile.copySlice (row * cw * 4) dst (((ty + row) * w + tx) * 4) (cw * 4)) dst

private theorem paintRows_size (w h cw ch tx ty : Nat) (dst tile : ByteArray)
    (hdst : dst.size = w * h * 4) (htile : tile.size = cw * ch * 4)
    (hx : tx + cw ≤ w) (hy : ty + ch ≤ h) (n : Nat) (hn : n ≤ ch) :
    (paintRows w cw ty tx tile dst n).size = dst.size := by
  induction n with
  | zero =>
    simp [paintRows, List.range_zero, List.foldl_nil]
  | succ n ih =>
    have hn' : n < ch := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have hle : n ≤ ch := Nat.le_of_lt hn'
    have hy' : ty + n < h := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hn' ty) hy
    unfold paintRows at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih hle
    have hsrc : n * cw * 4 + cw * 4 ≤ tile.size := by
      rw [htile]
      exact rowBytes_le cw ch n hn'
    have hoff : ((ty + n) * w + tx) * 4 + cw * 4 ≤
        ((List.range n).foldl (fun dst row =>
          tile.copySlice (row * cw * 4) dst (((ty + row) * w + tx) * 4) (cw * 4)) dst).size := by
      rw [hprev, hdst]
      exact rowOff_le w h tx ty cw n hx hy'
    rw [copySlice_size tile _ (n * cw * 4) (((ty + n) * w + tx) * 4) (cw * 4) hsrc hoff]
    exact hprev

private theorem paintRows_get (w h cw ch tx ty : Nat) (dst tile : ByteArray)
    (hdst : dst.size = w * h * 4) (htile : tile.size = cw * ch * 4)
    (hx : tx + cw ≤ w) (hy : ty + ch ≤ h) (i : Nat) (hi : i < dst.size)
    (hw : 0 < w) (hm : Window.missesByte ⟨tx, ty, cw, ch⟩ w i)
    (n : Nat) (hn : n ≤ ch) :
    (paintRows w cw ty tx tile dst n)[i]! = dst[i]! := by
  induction n with
  | zero =>
    simp [paintRows, List.range_zero, List.foldl_nil]
  | succ n ih =>
    have hn' : n < ch := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have hle : n ≤ ch := Nat.le_of_lt hn'
    have hprev := paintRows_size w h cw ch tx ty dst tile hdst htile hx hy n hle
    unfold paintRows
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hout := miss_outside_row w tx ty cw ch n i hw hx hn' hm
    have hsrc : n * cw * 4 + cw * 4 ≤ tile.size := by
      rw [htile]; exact rowBytes_le cw ch n hn'
    have hdoff : ((ty + n) * w + tx) * 4 + cw * 4 ≤ (paintRows w cw ty tx tile dst n).size := by
      rw [hprev, hdst]
      exact rowOff_le w h tx ty cw n hx (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hn' ty) hy)
    have hstep := copySlice_get tile (paintRows w cw ty tx tile dst n)
      (n * cw * 4) (((ty + n) * w + tx) * 4) (cw * 4) i hsrc hdoff
      (by rw [hprev]; exact hi) hout
    unfold paintRows at hstep
    rw [hstep]
    exact ih hle

theorem Tile.blit_size {w h cw ch tx ty : Nat} {dst tile : ByteArray}
    (hdst : dst.size = w * h * 4) (htile : tile.size = cw * ch * 4)
    (hx : tx + cw ≤ w) (hy : ty + ch ≤ h) :
    (Tile.blit dst w tile cw ch tx ty).size = dst.size := by
  simpa [Tile.blit, paintRows] using
    paintRows_size w h cw ch tx ty dst tile hdst htile hx hy ch (Nat.le_refl _)

theorem Tile.blit_get_outside {w h cw ch tx ty : Nat} {dst tile : ByteArray} {i : Nat}
    (hdst : dst.size = w * h * 4) (htile : tile.size = cw * ch * 4)
    (hx : tx + cw ≤ w) (hy : ty + ch ≤ h) (hi : i < dst.size)
    (hm : Window.missesByte ⟨tx, ty, cw, ch⟩ w i) :
    (Tile.blit dst w tile cw ch tx ty)[i]! = dst[i]! := by
  have hw : 0 < w := by
    cases w with
    | zero => simp [hdst] at hi
    | succ _ => exact Nat.succ_pos _
  simpa [Tile.blit, paintRows] using
    paintRows_get w h cw ch tx ty dst tile hdst htile hx hy i hi hw hm ch (Nat.le_refl _)

private theorem blitList_get {w h : Nat} {dst : ByteArray}
    (hdst : dst.size = w * h * 4) (ws : List Window) (tile : Window → ByteArray)
    (htile : ∀ win ∈ ws, (tile win).size = win.w * win.h * 4)
    (hfit : ∀ win ∈ ws, win.inside w h) (i : Nat) (hi : i < dst.size)
    (hm : ∀ win ∈ ws, Window.missesByte win w i) :
    (ws.foldl (fun data win =>
      Tile.blit data w (tile win) win.w win.h win.x win.y) dst)[i]! = dst[i]! := by
  induction ws generalizing dst with
  | nil => simp
  | cons win ws ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp] at htile hfit hm ⊢
    have hsize := Tile.blit_size (hdst := hdst) (htile := htile.1) hfit.1.1 hfit.1.2
    have hget := Tile.blit_get_outside (hdst := hdst) (htile := htile.1)
      hfit.1.1 hfit.1.2 hi hm.1
    rw [ih (hsize.trans hdst) htile.2 hfit.2 (by rw [hsize]; exact hi) hm.2]
    exact hget

private theorem eq_of_bne_false {a b : Nat} (h : (a != b) = false) : a = b := by
  by_cases hab : a = b
  · exact hab
  · have : (a != b) = true := by simp [hab]
    simp [this] at h

private theorem mem_full_window (w h : Nat) :
    (⟨0, 0, w, h⟩ : Window) ∈ (#[⟨0, 0, w, h⟩] : Array Window) := by
  refine Array.mem_iff_getElem.mpr ⟨0, ?_, ?_⟩
  · simp
  · simp

/-- Bytes that miss every window of `Frame.update` are the bytes of the
previous frame. A full redraw reports the whole frame as its only window, so
the hypothesis is empty there. -/
theorem Frame.update_get_outside
    (f : Frame) (w h : Nat) (ops : Array RenderOp) (bg : Color) (i : Nat)
    (hold : i < f.data.size)
    (hi : i < (update f w h ops bg).1.data.size)
    (hm : ∀ win ∈ (update f w h ops bg).2, Window.missesByte win w i) :
    (update f w h ops bg).1.data[i]! = f.data[i]! := by
  cases f with
  | mk fw fh fbg old data =>
    dsimp [Frame.update] at hi hm ⊢
    cases hcond : fw != w || fh != h || !(fbg == bg) || data.size != w * h * 4
    · -- Bool.false: same size and background, so a partial repaint is possible
      simp [hcond] at hi hm ⊢
      have hdata : data.size = w * h * 4 := by
        simp only [Bool.or_eq_false_iff] at hcond
        exact eq_of_bne_false hcond.2
      by_cases harea : w * h * 7 ≤
          Array.foldl (fun x1 x2 => x1 + x2.area) 0 (damage w h old ops) * 10
      · rw [ite_eq_left harea] at hi hm ⊢
        simp [Frame.full] at hi hm ⊢
        have hlen : i < w * h * 4 := by simpa [(Raster.render w h ops bg).hsize] using hi
        exact absurd hm (Window.full_not_miss w h i hlen)
      · rw [ite_eq_right harea] at hi hm ⊢
        rw [← Array.foldl_toList]
        exact blitList_get hdata (damage w h old ops).toList
          (fun r => (Raster.renderWindow r.x r.y r.w r.h
            ((TileList.build ops).select r.x r.y r.w r.h) bg).data)
          (by
            intro win _
            exact (Raster.renderWindow win.x win.y win.w win.h
              ((TileList.build ops).select win.x win.y win.w win.h) bg).hsize)
          (by
            intro win hmem
            exact damage_inside w h old ops win (Array.mem_toList_iff.mp hmem))
          i hold
          (by
            intro win hmem
            exact hm win (Array.mem_toList_iff.mp hmem))
    · -- Bool.true: size or background changed, one window covers the frame
      simp [hcond, Frame.full] at hi hm ⊢
      have hlen : i < w * h * 4 := by simpa [(Raster.render w h ops bg).hsize] using hi
      exact absurd hm (Window.full_not_miss w h i hlen)

end UVL

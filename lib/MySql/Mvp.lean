import Std.Tactic.Simpa

set_option profiler true

-- def f (h0 : Char) : Unit :=
--   let x := h0.val - '0'.val |>.toUInt8
--   if h: x < 24
--     then
--       have hh : x.toNat < 24 := by
--         -- exact h -- h -- by simpa [x] using h
--       ()
--     else
--       ()

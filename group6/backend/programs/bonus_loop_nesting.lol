HAI
  WAZZUP
    I HAS A row ITZ 1
    I HAS A col ITZ 1
    I HAS A prod ITZ 0
    I HAS A outer_n ITZ 3
    I HAS A inner_n ITZ 0
  BUHBYE

  BTW 1) Nested UPPIN/TIL loops printing a 3x3 multiplication table
  VISIBLE "--- 3x3 Multiplication Table ---"
  IM IN YR row_loop UPPIN YR row TIL BOTH SAEM row AN 4
    col R 1
    IM IN YR col_loop UPPIN YR col TIL BOTH SAEM col AN 4
      prod R PRODUKT OF row AN col
      VISIBLE row + " x " + col + " = " + prod
    IM OUTTA YR col_loop
  IM OUTTA YR row_loop

  BTW 2) Nested NERFIN/WILE loop with inner GTFO (only breaks inner loop)
  VISIBLE "--- Nested NERFIN with inner GTFO ---"
  IM IN YR countdown NERFIN YR outer_n WILE DIFFRINT outer_n AN 0
    inner_n R 1
    IM IN YR inner_step UPPIN YR inner_n TIL BOTH SAEM inner_n AN 5
      VISIBLE "outer=" + outer_n + " inner=" + inner_n
      BOTH SAEM inner_n AN 2
      O RLY?
        YA RLY
          GTFO
      OIC
    IM OUTTA YR inner_step
  IM OUTTA YR countdown

  VISIBLE "Loop nesting complete"
KTHXBYE

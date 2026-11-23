HAI
  WAZZUP
    I HAS A i ITZ 1
    I HAS A j ITZ 0
    I HAS A mode ITZ 2
  BUHBYE

  BTW 1) Loop -> If-Else -> Switch -> Inner Loop
  VISIBLE "--- Loop -> If -> Switch -> Loop ---"
  IM IN YR outer_loop UPPIN YR i TIL BOTH SAEM i AN 5
    BOTH SAEM i AN 4
    O RLY?
      YA RLY
        VISIBLE "Stopping outer_loop at i=4 via GTFO"
        GTFO
      MEBBE BOTH SAEM i AN 2
        VISIBLE "i=2 entering switch"
        mode
        WTF?
          OMG 1
            VISIBLE "mode 1"
            GTFO
          OMG 2
            j R 1
            IM IN YR inner_loop UPPIN YR j TIL BOTH SAEM j AN 4
              VISIBLE "  switch->loop step " + j
            IM OUTTA YR inner_loop
            GTFO
          OMGWTF
            VISIBLE "other mode"
        OIC
        VISIBLE "Resumed after switch inside MEBBE"
      NO WAI
        VISIBLE "Regular iteration i=" + i
    OIC
  IM OUTTA YR outer_loop

  BTW 2) Switch -> Loop -> If-Else
  VISIBLE "--- Switch -> Loop -> If ---"
  mode
  WTF?
    OMG 2
      j R 1
      IM IN YR parity_loop UPPIN YR j TIL BOTH SAEM j AN 5
        BOTH SAEM MOD OF j AN 2 AN 0
        O RLY?
          YA RLY
            VISIBLE j + " is even"
          NO WAI
            VISIBLE j + " is odd"
        OIC
      IM OUTTA YR parity_loop
      GTFO
    OMGWTF
      VISIBLE "Skipped"
  OIC

  VISIBLE "Mixed flow control nesting complete"
KTHXBYE

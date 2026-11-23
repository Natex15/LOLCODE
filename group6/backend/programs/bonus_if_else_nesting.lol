HAI
  WAZZUP
    I HAS A age ITZ 20
    I HAS A has_id ITZ WIN
    I HAS A is_vip ITZ FAIL
  BUHBYE

  BTW 1) Nested if-else inside YA RLY (3 levels deep)
  BOTH SAEM age AN BIGGR OF age AN 18
  O RLY?
    YA RLY
      VISIBLE "Adult check passed"
      has_id
      O RLY?
        YA RLY
          VISIBLE "ID check passed"
          is_vip
          O RLY?
            YA RLY
              VISIBLE "Access -> VIP lounge"
            NO WAI
              VISIBLE "Access -> General admission"
          OIC
        NO WAI
          VISIBLE "Access -> Denied (no ID)"
      OIC
    NO WAI
      VISIBLE "Access -> Denied (underage)"
  OIC

  BTW 2) Nested if-else inside MEBBE and NO WAI
  age R 15
  has_id R FAIL
  BOTH SAEM age AN BIGGR OF age AN 18
  O RLY?
    YA RLY
      VISIBLE "Adult"
    MEBBE BOTH SAEM age AN BIGGR OF age AN 13
      VISIBLE "Teen branch entered"
      has_id
      O RLY?
        YA RLY
          VISIBLE "Teen with student ID"
        NO WAI
          VISIBLE "Teen without student ID"
      OIC
    NO WAI
      is_vip
      O RLY?
        YA RLY
          VISIBLE "Child VIP"
        NO WAI
          VISIBLE "Child regular"
      OIC
  OIC

  BTW 3) Nested if-else inside NO WAI
  age R 8
  is_vip R WIN
  BOTH SAEM age AN BIGGR OF age AN 18
  O RLY?
    YA RLY
      VISIBLE "Adult"
    NO WAI
      is_vip
      O RLY?
        YA RLY
          VISIBLE "Minor with VIP pass"
        NO WAI
          VISIBLE "Minor without VIP pass"
      OIC
  OIC
KTHXBYE

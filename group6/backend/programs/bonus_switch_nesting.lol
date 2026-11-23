HAI
  WAZZUP
    I HAS A category ITZ "drink"
    I HAS A item ITZ 2
  BUHBYE

  BTW 1) Nested WTF? inside OMG; inner GTFO only exits inner switch
  category
  WTF?
    OMG "food"
      item
      WTF?
        OMG 1
          VISIBLE "Burger"
          GTFO
        OMG 2
          VISIBLE "Pizza"
          GTFO
        OMGWTF
          VISIBLE "Other food"
      OIC
      GTFO
    OMG "drink"
      item
      WTF?
        OMG 1
          VISIBLE "Water"
          GTFO
        OMG 2
          VISIBLE "Coffee"
          GTFO
        OMGWTF
          VISIBLE "Other drink"
      OIC
      VISIBLE "After inner switch (still in outer OMG drink)"
      GTFO
    OMGWTF
      VISIBLE "Unknown category"
  OIC

  BTW 2) Nested WTF? inside OMGWTF default case
  category R "dessert"
  item R 1
  category
  WTF?
    OMG "food"
      VISIBLE "Food"
      GTFO
    OMGWTF
      VISIBLE "Fallback category"
      item
      WTF?
        OMG 1
          VISIBLE "Fallback item -> Cake"
          GTFO
        OMGWTF
          VISIBLE "Fallback item -> Unknown"
      OIC
  OIC
KTHXBYE

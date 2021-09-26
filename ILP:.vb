ILP:
ILP 
  Minimise 
  ((:+) 
    ((:+) 
      (Constant Number {0}) 
      ((:*) 
        Number {1} 
        (Fused 
          (Label {_labelId = 0, _parent = Nothing}) 
          (Label {_labelId = 3, _parent = Nothing})
        )
      )
    )
    ((:*) 
      Number {1} 
      (Fused 
        (Label {_labelId = 3, _parent = Nothing}) 
        (Label {_labelId = 6, _parent = Nothing})
      )
    )
  )
  ((:&&) 
    ((:&&) 
      ((:&&) 
        TrueConstraint 
        ((:&&) 
          ((:&&) 
            ((:<=) 
              ((:*) 
                Number {1} 
                (Fused 
                  (Label {_labelId = 0, _parent = Nothing}) 
                  (Label {_labelId = 3, _parent = Nothing})
                )
              ) 
              ((:+) 
                ((:*) 
                  Number {1} 
                  (Pi 
                    (Label {_labelId = 3, _parent = Nothing})
                  )
                ) 
                ((:*) 
                  Number {(-1)} 
                  (Pi 
                    (Label {_labelId = 0, _parent = Nothing})
                  )
                )
              )
            ) 
            ((:<=) 
              ((:+) 
                ((:*) 
                  Number {1} 
                  (Pi 
                    (Label {_labelId = 3, _parent = Nothing})
                  )
                ) 
                ((:*) 
                  Number {(-1)} 
                  (Pi 
                    (Label {_labelId = 0, _parent = Nothing})
                  )
                )
              ) 
              ((:*) 
                Number {1} 
                (Fused 
                  (Label {_labelId = 0, _parent = Nothing}) 
                  (Label {_labelId = 3, _parent = Nothing})
                )
              )
            )
          ) 
          ((:&&) 
            ((:<=) 
              ((:*) 
                Number {1} 
                (Fused 
                  (Label {_labelId = 3, _parent = Nothing}) 
                  (Label {_labelId = 6, _parent = Nothing})
                )
              ) 
              ((:+) 
                ((:*) 
                  Number {1} 
                  (Pi 
                    (Label {_labelId = 6, _parent = Nothing})
                  )
                ) 
                ((:*) 
                  Number {(-1)} 
                  (Pi 
                    (Label {_labelId = 3, _parent = Nothing})
                  )
                )
              )
            ) 
            ((:<=) 
              ((:+) 
                ((:*) 
                  Number {1} 
                  (Pi 
                    (Label {_labelId = 6, _parent = Nothing})
                  )
                ) 
                ((:*) 
                  Number {(-1)} 
                  (Pi 
                    (Label {_labelId = 3, _parent = Nothing})
                  )
                )
              ) 
              ((:*) 
                Number {1} 
                (Fused 
                  (Label {_labelId = 3, _parent = Nothing}) 
                  (Label {_labelId = 6, _parent = Nothing})
                )
              )
            )
          )
        )
      ) 
      ((:&&) 
        ((:&&) 
          ((:>=) 
            ((:+) 
              ((:*) 
                Number {1} 
                (Pi 
                  (Label {_labelId = 2, _parent = Nothing})
                )
              ) 
              ((:*) 
                Number {(-1)} 
                (Pi 
                  (Label {_labelId = 0, _parent = Nothing})
                )
              )
            ) 
            (Constant Number {1})
          ) 
          ((:&&) 
            ((:>=) 
              ((:+) 
                ((:*) 
                  Number {1} 
                  (Pi 
                    (Label {_labelId = 5, _parent = Nothing})
                  )
                ) 
                ((:*) 
                  Number {(-1)} 
                  (Pi 
                    (Label {_labelId = 0, _parent = Nothing})
                  )
                )
              ) 
              (Constant Number {1})
            ) 
            TrueConstraint
          )
        ) 
        ((:&&) 
          ((:>=) 
            ((:+) 
              ((:*) 
                Number {1} 
                (Pi 
                  (Label {_labelId = 7, _parent = Nothing})
                )
              ) 
              ((:*) 
                Number {(-1)} 
                (Pi 
                  (Label {_labelId = 0, _parent = Nothing})
                )
              )
            ) 
            (Constant Number {1})
          ) 
          ((:&&) 
            ((:&&) 
              ((:>=) 
                ((:+) 
                  ((:*) 
                    Number {1} 
                    (Pi 
                      (Label {_labelId = 7, _parent = Nothing})
                    )
                  ) 
                  ((:*) 
                    Number {(-1)} 
                    (Pi 
                      (Label {_labelId = 1, _parent = Nothing})
                    )
                  )
                ) 
                (Constant Number {1})
              ) 
              ((:&&) 
                ((:>=) 
                  ((:+) 
                    ((:*) 
                      Number {1} 
                      (Pi 
                        (Label {_labelId = 1, _parent = Nothing})
                      )
                    ) 
                    ((:*) 
                      Number {(-1)} 
                      (Pi 
                        (Label {_labelId = 2, _parent = Nothing})
                      )
                    )
                  ) 
                  (Constant Number {1})
                ) 
                ((:>=) 
                  ((:+) 
                    ((:*) 
                      Number {1} 
                      (Pi 
                        (Label {_labelId = 7, _parent = Nothing})
                      )
                    ) 
                    ((:*) 
                      Number {(-1)} 
                      (Pi 
                        (Label {_labelId = 4, _parent = Nothing})
                      )
                    )
                  ) 
                  (Constant Number {1})
                )
              )
            ) 
            ((:&&) 
              ((:>=) 
                ((:+) 
                  ((:*) 
                    Number {1} 
                    (Pi 
                      (Label {_labelId = 4, _parent = Nothing})
                    )
                  ) 
                  ((:*) 
                    Number {(-1)} 
                    (Pi 
                      (Label {_labelId = 5, _parent = Nothing})
                    )
                  )
                ) 
                (Constant Number {1})
              ) 
              ((:>=) 
                ((:+) 
                  ((:*) 
                    Number {1} 
                    (Pi 
                      (Label {_labelId = 7, _parent = Nothing})
                    )
                  ) 
                  ((:*) 
                    Number {(-1)} 
                    (Pi 
                      (Label {_labelId = 6, _parent = Nothing})
                    )
                  )
                ) 
                (Constant Number {1})
              )
            )
          )
        )
      )
    ) 
    ((:&&) 
      TrueConstraint 
      ((:&&) 
        ((:&&) 
          ((:&&) 
            ((:>=) 
              ((:*) 
                Number {1} 
                  (Fused 
                    (Label {_labelId = 0, _parent = Nothing}) 
                    (Label {_labelId = 3, _parent = Nothing})
                  )
                ) 
                ((:+) 
                  ((:*) 
                    Number {1} 
                    (BackendSpecific (OrderIn (Label {_labelId = 3, _parent = Nothing})))
                  ) 
                  ((:*) 
                    Number {(-1)} 
                    (BackendSpecific (OrderOut (Label {_labelId = 0, _parent = Nothing})))
                  )
                )
              ) 
              ((:<=) 
                ((:*) 
                  Number {(-1)} 
                  (Fused 
                    (Label {_labelId = 0, _parent = Nothing}) 
                    (Label {_labelId = 3, _parent = Nothing})
                  )
                ) 
                ((:+) 
                  ((:*) 
                    Number {1} 
                    (BackendSpecific (OrderIn (Label {_labelId = 3, _parent = Nothing})))
                  ) 
                  ((:*) 
                    Number {(-1)} 
                    (BackendSpecific (OrderOut (Label {_labelId = 0, _parent = Nothing})))
                  )
                )
              )
            ) 
            ((:==) 
              ((:*) 
                Number {1} 
                (BackendSpecific (OrderIn (Label {_labelId = 3, _parent = Nothing})))
              ) 
              ((:*) 
                Number {1} 
                (BackendSpecific (OrderOut (Label {_labelId = 3, _parent = Nothing})))
              )
            )
          ) 
          ((:&&) 
            TrueConstraint 
            ((:&&) 
              ((:&&) 
                ((:&&) 
                  ((:>=) 
                    ((:*) 
                      Number {1} 
                      (Fused 
                        (Label {_labelId = 3, _parent = Nothing}) 
                        (Label {_labelId = 6, _parent = Nothing})
                      )
                    ) 
                    ((:+) 
                      ((:*) 
                        Number {1} 
                        (BackendSpecific (OrderIn (Label {_labelId = 6, _parent = Nothing})))
                      ) 
                      ((:*) 
                        Number {(-1)} 
                        (BackendSpecific (OrderOut (Label {_labelId = 3, _parent = Nothing})))
                      )
                    )
                  ) 
                  ((:<=) 
                    ((:*) 
                      Number {(-1)} 
                      (Fused 
                        (Label {_labelId = 3, _parent = Nothing}) 
                        (Label {_labelId = 6, _parent = Nothing})
                      )
                    ) 
                    ((:+) 
                      ((:*) 
                        Number {1} 
                        (BackendSpecific (OrderIn (Label {_labelId = 6, _parent = Nothing})))
                      )
                      ((:*) 
                        Number {(-1)} 
                        (BackendSpecific (OrderOut (Label {_labelId = 3, _parent = Nothing})))
                      )
                    )
                  )
                ) 
                ((:==) 
                  ((:*) 
                    Number {1} 
                    (BackendSpecific (OrderIn (Label {_labelId = 6, _parent = Nothing})))
                  ) 
                  ((:*) 
                    Number {1} 
                    (BackendSpecific (OrderOut (Label {_labelId = 6, _parent = Nothing})))
                  )
                )
              ) 
              TrueConstraint
            )
          )
        )
      )
    ) 
    ((:<>) 
      ((:<>) 
        ((:<>) 
          (LowerUpper 
            0 
            (Pi 
              (Label {_labelId = 3, _parent = Nothing})
            ) 
            2
          ) 
          ((:<>) 
            (LowerUpper 
              0
              (Pi 
                (Label {_labelId = 6, _parent = Nothing})
              ) 
              2
            ) 
            NoBounds
          )
        ) 
        ((:<>) 
          (Binary 
            (Fused 
              (Label {_labelId = 0, _parent = Nothing}) 
              (Label {_labelId = 3, _parent = Nothing})
            )
          ) 
          ((:<>) 
            (Binary 
              (Fused 
                (Label {_labelId = 3, _parent = Nothing}) 
                (Label {_labelId = 6, _parent = Nothing})
              )
            ) 
            NoBounds
          )
        )
      ) 
      ((:<>) 
        NoBounds 
        ((:<>) 
          ((:<>) 
            (Lower 
              (-2) 
              (BackendSpecific (OrderIn (Label {_labelId = 3, _parent = Nothing})))
            ) 
            (Lower (-2) (BackendSpecific (OrderOut (Label {_labelId = 3, _parent = Nothing})))
          )
        ) 
        ((:<>) 
          NoBounds 
          ((:<>) 
            ((:<>) 
              (Lower 
                (-2) 
                (BackendSpecific (OrderIn (Label {_labelId = 6, _parent = Nothing})))
              )
              (Lower 
                (-2) 
                (BackendSpecific (OrderOut (Label {_labelId = 6, _parent = Nothing})))
              )
            ) 
            NoBounds
          )
        )
      )
    )
  ) 
  2
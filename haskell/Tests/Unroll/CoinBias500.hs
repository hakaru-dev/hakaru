{-# LANGUAGE DataKinds, TypeOperators, OverloadedStrings #-}

module CoinBias500 where

import Prelude (print, length, IO)
import Language.Hakaru.Syntax.Prelude
import Language.Hakaru.Disintegrate
import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

type Model a b = TrivialABT Term '[] ('HMeasure (HPair a b))
type Cond  a b = TrivialABT Term '[] (a ':-> 'HMeasure b)

coinBias :: Model (HPair HBool 
                   (HPair HBool 
                    (HPair HBool 
                     (HPair HBool 
                      (HPair HBool 
                       (HPair HBool 
                        (HPair HBool 
                         (HPair HBool 
                          (HPair HBool 
                           (HPair HBool 
                            (HPair HBool 
                             (HPair HBool 
                              (HPair HBool 
                               (HPair HBool 
                                (HPair HBool 
                                 (HPair HBool 
                                  (HPair HBool 
                                   (HPair HBool 
                                    (HPair HBool 
                                     (HPair HBool 
                                      (HPair HBool 
                                       (HPair HBool 
                                        (HPair HBool 
                                         (HPair HBool 
                                          (HPair HBool 
                                           (HPair HBool 
                                            (HPair HBool 
                                             (HPair HBool 
                                              (HPair HBool 
                                               (HPair HBool 
                                                (HPair HBool 
                                                 (HPair HBool 
                                                  (HPair HBool 
                                                   (HPair HBool 
                                                    (HPair HBool 
                                                     (HPair HBool 
                                                      (HPair HBool 
                                                       (HPair HBool 
                                                        (HPair HBool 
                                                         (HPair HBool 
                                                          (HPair HBool 
                                                           (HPair HBool 
                                                            (HPair HBool 
                                                             (HPair HBool 
                                                              (HPair HBool 
                                                               (HPair HBool 
                                                                (HPair HBool 
                                                                 (HPair HBool 
                                                                  (HPair HBool 
                                                                   (HPair HBool 
                                                                    (HPair HBool 
                                                                     (HPair HBool 
                                                                      (HPair HBool 
                                                                       (HPair HBool 
                                                                        (HPair HBool 
                                                                         (HPair HBool 
                                                                          (HPair HBool 
                                                                           (HPair HBool 
                                                                            (HPair HBool 
                                                                             (HPair HBool 
                                                                              (HPair HBool 
                                                                               (HPair HBool 
                                                                                (HPair HBool 
                                                                                 (HPair HBool 
                                                                                  (HPair HBool 
                                                                                   (HPair HBool 
                                                                                    (HPair HBool 
                                                                                     (HPair HBool 
                                                                                      (HPair HBool 
                                                                                       (HPair HBool 
                                                                                        (HPair HBool 
                                                                                         (HPair HBool 
                                                                                          (HPair HBool 
                                                                                           (HPair HBool 
                                                                                            (HPair HBool 
                                                                                             (HPair HBool 
                                                                                              (HPair HBool 
                                                                                               (HPair HBool 
                                                                                                (HPair HBool 
                                                                                                 (HPair HBool 
                                                                                                  (HPair HBool 
                                                                                                   (HPair HBool 
                                                                                                    (HPair HBool 
                                                                                                     (HPair HBool 
                                                                                                      (HPair HBool 
                                                                                                       (HPair HBool 
                                                                                                        (HPair HBool 
                                                                                                         (HPair HBool 
                                                                                                          (HPair HBool 
                                                                                                           (HPair HBool 
                                                                                                            (HPair HBool 
                                                                                                             (HPair HBool 
                                                                                                              (HPair HBool 
                                                                                                               (HPair HBool 
                                                                                                                (HPair HBool 
                                                                                                                 (HPair HBool 
                                                                                                                  (HPair HBool 
                                                                                                                   (HPair HBool 
                                                                                                                    (HPair HBool 
                                                                                                                     (HPair HBool 
                                                                                                                      (HPair HBool 
                                                                                                                       (HPair HBool 
                                                                                                                        (HPair HBool 
                                                                                                                         (HPair HBool 
                                                                                                                          (HPair HBool 
                                                                                                                           (HPair HBool 
                                                                                                                            (HPair HBool 
                                                                                                                             (HPair HBool 
                                                                                                                              (HPair HBool 
                                                                                                                               (HPair HBool 
                                                                                                                                (HPair HBool 
                                                                                                                                 (HPair HBool 
                                                                                                                                  (HPair HBool 
                                                                                                                                   (HPair HBool 
                                                                                                                                    (HPair HBool 
                                                                                                                                     (HPair HBool 
                                                                                                                                      (HPair HBool 
                                                                                                                                       (HPair HBool 
                                                                                                                                        (HPair HBool 
                                                                                                                                         (HPair HBool 
                                                                                                                                          (HPair HBool 
                                                                                                                                           (HPair HBool 
                                                                                                                                            (HPair HBool 
                                                                                                                                             (HPair HBool 
                                                                                                                                              (HPair HBool 
                                                                                                                                               (HPair HBool 
                                                                                                                                                (HPair HBool 
                                                                                                                                                 (HPair HBool 
                                                                                                                                                  (HPair HBool 
                                                                                                                                                   (HPair HBool 
                                                                                                                                                    (HPair HBool 
                                                                                                                                                     (HPair HBool 
                                                                                                                                                      (HPair HBool 
                                                                                                                                                       (HPair HBool 
                                                                                                                                                        (HPair HBool 
                                                                                                                                                         (HPair HBool 
                                                                                                                                                          (HPair HBool 
                                                                                                                                                           (HPair HBool 
                                                                                                                                                            (HPair HBool 
                                                                                                                                                             (HPair HBool 
                                                                                                                                                              (HPair HBool 
                                                                                                                                                               (HPair HBool 
                                                                                                                                                                (HPair HBool 
                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (HPair HBool 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     HBool)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            'HProb
coinBias =
    beta (prob_ 2) (prob_ 5) >>= \bias ->
    bern bias >>= \tossResult0 ->
    bern bias >>= \tossResult1 ->
    bern bias >>= \tossResult2 ->
    bern bias >>= \tossResult3 ->
    bern bias >>= \tossResult4 ->
    bern bias >>= \tossResult5 ->
    bern bias >>= \tossResult6 ->
    bern bias >>= \tossResult7 ->
    bern bias >>= \tossResult8 ->
    bern bias >>= \tossResult9 ->
    bern bias >>= \tossResult10 ->
    bern bias >>= \tossResult11 ->
    bern bias >>= \tossResult12 ->
    bern bias >>= \tossResult13 ->
    bern bias >>= \tossResult14 ->
    bern bias >>= \tossResult15 ->
    bern bias >>= \tossResult16 ->
    bern bias >>= \tossResult17 ->
    bern bias >>= \tossResult18 ->
    bern bias >>= \tossResult19 ->
    bern bias >>= \tossResult20 ->
    bern bias >>= \tossResult21 ->
    bern bias >>= \tossResult22 ->
    bern bias >>= \tossResult23 ->
    bern bias >>= \tossResult24 ->
    bern bias >>= \tossResult25 ->
    bern bias >>= \tossResult26 ->
    bern bias >>= \tossResult27 ->
    bern bias >>= \tossResult28 ->
    bern bias >>= \tossResult29 ->
    bern bias >>= \tossResult30 ->
    bern bias >>= \tossResult31 ->
    bern bias >>= \tossResult32 ->
    bern bias >>= \tossResult33 ->
    bern bias >>= \tossResult34 ->
    bern bias >>= \tossResult35 ->
    bern bias >>= \tossResult36 ->
    bern bias >>= \tossResult37 ->
    bern bias >>= \tossResult38 ->
    bern bias >>= \tossResult39 ->
    bern bias >>= \tossResult40 ->
    bern bias >>= \tossResult41 ->
    bern bias >>= \tossResult42 ->
    bern bias >>= \tossResult43 ->
    bern bias >>= \tossResult44 ->
    bern bias >>= \tossResult45 ->
    bern bias >>= \tossResult46 ->
    bern bias >>= \tossResult47 ->
    bern bias >>= \tossResult48 ->
    bern bias >>= \tossResult49 ->
    bern bias >>= \tossResult50 ->
    bern bias >>= \tossResult51 ->
    bern bias >>= \tossResult52 ->
    bern bias >>= \tossResult53 ->
    bern bias >>= \tossResult54 ->
    bern bias >>= \tossResult55 ->
    bern bias >>= \tossResult56 ->
    bern bias >>= \tossResult57 ->
    bern bias >>= \tossResult58 ->
    bern bias >>= \tossResult59 ->
    bern bias >>= \tossResult60 ->
    bern bias >>= \tossResult61 ->
    bern bias >>= \tossResult62 ->
    bern bias >>= \tossResult63 ->
    bern bias >>= \tossResult64 ->
    bern bias >>= \tossResult65 ->
    bern bias >>= \tossResult66 ->
    bern bias >>= \tossResult67 ->
    bern bias >>= \tossResult68 ->
    bern bias >>= \tossResult69 ->
    bern bias >>= \tossResult70 ->
    bern bias >>= \tossResult71 ->
    bern bias >>= \tossResult72 ->
    bern bias >>= \tossResult73 ->
    bern bias >>= \tossResult74 ->
    bern bias >>= \tossResult75 ->
    bern bias >>= \tossResult76 ->
    bern bias >>= \tossResult77 ->
    bern bias >>= \tossResult78 ->
    bern bias >>= \tossResult79 ->
    bern bias >>= \tossResult80 ->
    bern bias >>= \tossResult81 ->
    bern bias >>= \tossResult82 ->
    bern bias >>= \tossResult83 ->
    bern bias >>= \tossResult84 ->
    bern bias >>= \tossResult85 ->
    bern bias >>= \tossResult86 ->
    bern bias >>= \tossResult87 ->
    bern bias >>= \tossResult88 ->
    bern bias >>= \tossResult89 ->
    bern bias >>= \tossResult90 ->
    bern bias >>= \tossResult91 ->
    bern bias >>= \tossResult92 ->
    bern bias >>= \tossResult93 ->
    bern bias >>= \tossResult94 ->
    bern bias >>= \tossResult95 ->
    bern bias >>= \tossResult96 ->
    bern bias >>= \tossResult97 ->
    bern bias >>= \tossResult98 ->
    bern bias >>= \tossResult99 ->
    bern bias >>= \tossResult100 ->
    bern bias >>= \tossResult101 ->
    bern bias >>= \tossResult102 ->
    bern bias >>= \tossResult103 ->
    bern bias >>= \tossResult104 ->
    bern bias >>= \tossResult105 ->
    bern bias >>= \tossResult106 ->
    bern bias >>= \tossResult107 ->
    bern bias >>= \tossResult108 ->
    bern bias >>= \tossResult109 ->
    bern bias >>= \tossResult110 ->
    bern bias >>= \tossResult111 ->
    bern bias >>= \tossResult112 ->
    bern bias >>= \tossResult113 ->
    bern bias >>= \tossResult114 ->
    bern bias >>= \tossResult115 ->
    bern bias >>= \tossResult116 ->
    bern bias >>= \tossResult117 ->
    bern bias >>= \tossResult118 ->
    bern bias >>= \tossResult119 ->
    bern bias >>= \tossResult120 ->
    bern bias >>= \tossResult121 ->
    bern bias >>= \tossResult122 ->
    bern bias >>= \tossResult123 ->
    bern bias >>= \tossResult124 ->
    bern bias >>= \tossResult125 ->
    bern bias >>= \tossResult126 ->
    bern bias >>= \tossResult127 ->
    bern bias >>= \tossResult128 ->
    bern bias >>= \tossResult129 ->
    bern bias >>= \tossResult130 ->
    bern bias >>= \tossResult131 ->
    bern bias >>= \tossResult132 ->
    bern bias >>= \tossResult133 ->
    bern bias >>= \tossResult134 ->
    bern bias >>= \tossResult135 ->
    bern bias >>= \tossResult136 ->
    bern bias >>= \tossResult137 ->
    bern bias >>= \tossResult138 ->
    bern bias >>= \tossResult139 ->
    bern bias >>= \tossResult140 ->
    bern bias >>= \tossResult141 ->
    bern bias >>= \tossResult142 ->
    bern bias >>= \tossResult143 ->
    bern bias >>= \tossResult144 ->
    bern bias >>= \tossResult145 ->
    bern bias >>= \tossResult146 ->
    bern bias >>= \tossResult147 ->
    bern bias >>= \tossResult148 ->
    bern bias >>= \tossResult149 ->
    bern bias >>= \tossResult150 ->
    bern bias >>= \tossResult151 ->
    bern bias >>= \tossResult152 ->
    bern bias >>= \tossResult153 ->
    bern bias >>= \tossResult154 ->
    bern bias >>= \tossResult155 ->
    bern bias >>= \tossResult156 ->
    bern bias >>= \tossResult157 ->
    bern bias >>= \tossResult158 ->
    bern bias >>= \tossResult159 ->
    bern bias >>= \tossResult160 ->
    bern bias >>= \tossResult161 ->
    bern bias >>= \tossResult162 ->
    bern bias >>= \tossResult163 ->
    bern bias >>= \tossResult164 ->
    bern bias >>= \tossResult165 ->
    bern bias >>= \tossResult166 ->
    bern bias >>= \tossResult167 ->
    bern bias >>= \tossResult168 ->
    bern bias >>= \tossResult169 ->
    bern bias >>= \tossResult170 ->
    bern bias >>= \tossResult171 ->
    bern bias >>= \tossResult172 ->
    bern bias >>= \tossResult173 ->
    bern bias >>= \tossResult174 ->
    bern bias >>= \tossResult175 ->
    bern bias >>= \tossResult176 ->
    bern bias >>= \tossResult177 ->
    bern bias >>= \tossResult178 ->
    bern bias >>= \tossResult179 ->
    bern bias >>= \tossResult180 ->
    bern bias >>= \tossResult181 ->
    bern bias >>= \tossResult182 ->
    bern bias >>= \tossResult183 ->
    bern bias >>= \tossResult184 ->
    bern bias >>= \tossResult185 ->
    bern bias >>= \tossResult186 ->
    bern bias >>= \tossResult187 ->
    bern bias >>= \tossResult188 ->
    bern bias >>= \tossResult189 ->
    bern bias >>= \tossResult190 ->
    bern bias >>= \tossResult191 ->
    bern bias >>= \tossResult192 ->
    bern bias >>= \tossResult193 ->
    bern bias >>= \tossResult194 ->
    bern bias >>= \tossResult195 ->
    bern bias >>= \tossResult196 ->
    bern bias >>= \tossResult197 ->
    bern bias >>= \tossResult198 ->
    bern bias >>= \tossResult199 ->
    bern bias >>= \tossResult200 ->
    bern bias >>= \tossResult201 ->
    bern bias >>= \tossResult202 ->
    bern bias >>= \tossResult203 ->
    bern bias >>= \tossResult204 ->
    bern bias >>= \tossResult205 ->
    bern bias >>= \tossResult206 ->
    bern bias >>= \tossResult207 ->
    bern bias >>= \tossResult208 ->
    bern bias >>= \tossResult209 ->
    bern bias >>= \tossResult210 ->
    bern bias >>= \tossResult211 ->
    bern bias >>= \tossResult212 ->
    bern bias >>= \tossResult213 ->
    bern bias >>= \tossResult214 ->
    bern bias >>= \tossResult215 ->
    bern bias >>= \tossResult216 ->
    bern bias >>= \tossResult217 ->
    bern bias >>= \tossResult218 ->
    bern bias >>= \tossResult219 ->
    bern bias >>= \tossResult220 ->
    bern bias >>= \tossResult221 ->
    bern bias >>= \tossResult222 ->
    bern bias >>= \tossResult223 ->
    bern bias >>= \tossResult224 ->
    bern bias >>= \tossResult225 ->
    bern bias >>= \tossResult226 ->
    bern bias >>= \tossResult227 ->
    bern bias >>= \tossResult228 ->
    bern bias >>= \tossResult229 ->
    bern bias >>= \tossResult230 ->
    bern bias >>= \tossResult231 ->
    bern bias >>= \tossResult232 ->
    bern bias >>= \tossResult233 ->
    bern bias >>= \tossResult234 ->
    bern bias >>= \tossResult235 ->
    bern bias >>= \tossResult236 ->
    bern bias >>= \tossResult237 ->
    bern bias >>= \tossResult238 ->
    bern bias >>= \tossResult239 ->
    bern bias >>= \tossResult240 ->
    bern bias >>= \tossResult241 ->
    bern bias >>= \tossResult242 ->
    bern bias >>= \tossResult243 ->
    bern bias >>= \tossResult244 ->
    bern bias >>= \tossResult245 ->
    bern bias >>= \tossResult246 ->
    bern bias >>= \tossResult247 ->
    bern bias >>= \tossResult248 ->
    bern bias >>= \tossResult249 ->
    bern bias >>= \tossResult250 ->
    bern bias >>= \tossResult251 ->
    bern bias >>= \tossResult252 ->
    bern bias >>= \tossResult253 ->
    bern bias >>= \tossResult254 ->
    bern bias >>= \tossResult255 ->
    bern bias >>= \tossResult256 ->
    bern bias >>= \tossResult257 ->
    bern bias >>= \tossResult258 ->
    bern bias >>= \tossResult259 ->
    bern bias >>= \tossResult260 ->
    bern bias >>= \tossResult261 ->
    bern bias >>= \tossResult262 ->
    bern bias >>= \tossResult263 ->
    bern bias >>= \tossResult264 ->
    bern bias >>= \tossResult265 ->
    bern bias >>= \tossResult266 ->
    bern bias >>= \tossResult267 ->
    bern bias >>= \tossResult268 ->
    bern bias >>= \tossResult269 ->
    bern bias >>= \tossResult270 ->
    bern bias >>= \tossResult271 ->
    bern bias >>= \tossResult272 ->
    bern bias >>= \tossResult273 ->
    bern bias >>= \tossResult274 ->
    bern bias >>= \tossResult275 ->
    bern bias >>= \tossResult276 ->
    bern bias >>= \tossResult277 ->
    bern bias >>= \tossResult278 ->
    bern bias >>= \tossResult279 ->
    bern bias >>= \tossResult280 ->
    bern bias >>= \tossResult281 ->
    bern bias >>= \tossResult282 ->
    bern bias >>= \tossResult283 ->
    bern bias >>= \tossResult284 ->
    bern bias >>= \tossResult285 ->
    bern bias >>= \tossResult286 ->
    bern bias >>= \tossResult287 ->
    bern bias >>= \tossResult288 ->
    bern bias >>= \tossResult289 ->
    bern bias >>= \tossResult290 ->
    bern bias >>= \tossResult291 ->
    bern bias >>= \tossResult292 ->
    bern bias >>= \tossResult293 ->
    bern bias >>= \tossResult294 ->
    bern bias >>= \tossResult295 ->
    bern bias >>= \tossResult296 ->
    bern bias >>= \tossResult297 ->
    bern bias >>= \tossResult298 ->
    bern bias >>= \tossResult299 ->
    bern bias >>= \tossResult300 ->
    bern bias >>= \tossResult301 ->
    bern bias >>= \tossResult302 ->
    bern bias >>= \tossResult303 ->
    bern bias >>= \tossResult304 ->
    bern bias >>= \tossResult305 ->
    bern bias >>= \tossResult306 ->
    bern bias >>= \tossResult307 ->
    bern bias >>= \tossResult308 ->
    bern bias >>= \tossResult309 ->
    bern bias >>= \tossResult310 ->
    bern bias >>= \tossResult311 ->
    bern bias >>= \tossResult312 ->
    bern bias >>= \tossResult313 ->
    bern bias >>= \tossResult314 ->
    bern bias >>= \tossResult315 ->
    bern bias >>= \tossResult316 ->
    bern bias >>= \tossResult317 ->
    bern bias >>= \tossResult318 ->
    bern bias >>= \tossResult319 ->
    bern bias >>= \tossResult320 ->
    bern bias >>= \tossResult321 ->
    bern bias >>= \tossResult322 ->
    bern bias >>= \tossResult323 ->
    bern bias >>= \tossResult324 ->
    bern bias >>= \tossResult325 ->
    bern bias >>= \tossResult326 ->
    bern bias >>= \tossResult327 ->
    bern bias >>= \tossResult328 ->
    bern bias >>= \tossResult329 ->
    bern bias >>= \tossResult330 ->
    bern bias >>= \tossResult331 ->
    bern bias >>= \tossResult332 ->
    bern bias >>= \tossResult333 ->
    bern bias >>= \tossResult334 ->
    bern bias >>= \tossResult335 ->
    bern bias >>= \tossResult336 ->
    bern bias >>= \tossResult337 ->
    bern bias >>= \tossResult338 ->
    bern bias >>= \tossResult339 ->
    bern bias >>= \tossResult340 ->
    bern bias >>= \tossResult341 ->
    bern bias >>= \tossResult342 ->
    bern bias >>= \tossResult343 ->
    bern bias >>= \tossResult344 ->
    bern bias >>= \tossResult345 ->
    bern bias >>= \tossResult346 ->
    bern bias >>= \tossResult347 ->
    bern bias >>= \tossResult348 ->
    bern bias >>= \tossResult349 ->
    bern bias >>= \tossResult350 ->
    bern bias >>= \tossResult351 ->
    bern bias >>= \tossResult352 ->
    bern bias >>= \tossResult353 ->
    bern bias >>= \tossResult354 ->
    bern bias >>= \tossResult355 ->
    bern bias >>= \tossResult356 ->
    bern bias >>= \tossResult357 ->
    bern bias >>= \tossResult358 ->
    bern bias >>= \tossResult359 ->
    bern bias >>= \tossResult360 ->
    bern bias >>= \tossResult361 ->
    bern bias >>= \tossResult362 ->
    bern bias >>= \tossResult363 ->
    bern bias >>= \tossResult364 ->
    bern bias >>= \tossResult365 ->
    bern bias >>= \tossResult366 ->
    bern bias >>= \tossResult367 ->
    bern bias >>= \tossResult368 ->
    bern bias >>= \tossResult369 ->
    bern bias >>= \tossResult370 ->
    bern bias >>= \tossResult371 ->
    bern bias >>= \tossResult372 ->
    bern bias >>= \tossResult373 ->
    bern bias >>= \tossResult374 ->
    bern bias >>= \tossResult375 ->
    bern bias >>= \tossResult376 ->
    bern bias >>= \tossResult377 ->
    bern bias >>= \tossResult378 ->
    bern bias >>= \tossResult379 ->
    bern bias >>= \tossResult380 ->
    bern bias >>= \tossResult381 ->
    bern bias >>= \tossResult382 ->
    bern bias >>= \tossResult383 ->
    bern bias >>= \tossResult384 ->
    bern bias >>= \tossResult385 ->
    bern bias >>= \tossResult386 ->
    bern bias >>= \tossResult387 ->
    bern bias >>= \tossResult388 ->
    bern bias >>= \tossResult389 ->
    bern bias >>= \tossResult390 ->
    bern bias >>= \tossResult391 ->
    bern bias >>= \tossResult392 ->
    bern bias >>= \tossResult393 ->
    bern bias >>= \tossResult394 ->
    bern bias >>= \tossResult395 ->
    bern bias >>= \tossResult396 ->
    bern bias >>= \tossResult397 ->
    bern bias >>= \tossResult398 ->
    bern bias >>= \tossResult399 ->
    bern bias >>= \tossResult400 ->
    bern bias >>= \tossResult401 ->
    bern bias >>= \tossResult402 ->
    bern bias >>= \tossResult403 ->
    bern bias >>= \tossResult404 ->
    bern bias >>= \tossResult405 ->
    bern bias >>= \tossResult406 ->
    bern bias >>= \tossResult407 ->
    bern bias >>= \tossResult408 ->
    bern bias >>= \tossResult409 ->
    bern bias >>= \tossResult410 ->
    bern bias >>= \tossResult411 ->
    bern bias >>= \tossResult412 ->
    bern bias >>= \tossResult413 ->
    bern bias >>= \tossResult414 ->
    bern bias >>= \tossResult415 ->
    bern bias >>= \tossResult416 ->
    bern bias >>= \tossResult417 ->
    bern bias >>= \tossResult418 ->
    bern bias >>= \tossResult419 ->
    bern bias >>= \tossResult420 ->
    bern bias >>= \tossResult421 ->
    bern bias >>= \tossResult422 ->
    bern bias >>= \tossResult423 ->
    bern bias >>= \tossResult424 ->
    bern bias >>= \tossResult425 ->
    bern bias >>= \tossResult426 ->
    bern bias >>= \tossResult427 ->
    bern bias >>= \tossResult428 ->
    bern bias >>= \tossResult429 ->
    bern bias >>= \tossResult430 ->
    bern bias >>= \tossResult431 ->
    bern bias >>= \tossResult432 ->
    bern bias >>= \tossResult433 ->
    bern bias >>= \tossResult434 ->
    bern bias >>= \tossResult435 ->
    bern bias >>= \tossResult436 ->
    bern bias >>= \tossResult437 ->
    bern bias >>= \tossResult438 ->
    bern bias >>= \tossResult439 ->
    bern bias >>= \tossResult440 ->
    bern bias >>= \tossResult441 ->
    bern bias >>= \tossResult442 ->
    bern bias >>= \tossResult443 ->
    bern bias >>= \tossResult444 ->
    bern bias >>= \tossResult445 ->
    bern bias >>= \tossResult446 ->
    bern bias >>= \tossResult447 ->
    bern bias >>= \tossResult448 ->
    bern bias >>= \tossResult449 ->
    bern bias >>= \tossResult450 ->
    bern bias >>= \tossResult451 ->
    bern bias >>= \tossResult452 ->
    bern bias >>= \tossResult453 ->
    bern bias >>= \tossResult454 ->
    bern bias >>= \tossResult455 ->
    bern bias >>= \tossResult456 ->
    bern bias >>= \tossResult457 ->
    bern bias >>= \tossResult458 ->
    bern bias >>= \tossResult459 ->
    bern bias >>= \tossResult460 ->
    bern bias >>= \tossResult461 ->
    bern bias >>= \tossResult462 ->
    bern bias >>= \tossResult463 ->
    bern bias >>= \tossResult464 ->
    bern bias >>= \tossResult465 ->
    bern bias >>= \tossResult466 ->
    bern bias >>= \tossResult467 ->
    bern bias >>= \tossResult468 ->
    bern bias >>= \tossResult469 ->
    bern bias >>= \tossResult470 ->
    bern bias >>= \tossResult471 ->
    bern bias >>= \tossResult472 ->
    bern bias >>= \tossResult473 ->
    bern bias >>= \tossResult474 ->
    bern bias >>= \tossResult475 ->
    bern bias >>= \tossResult476 ->
    bern bias >>= \tossResult477 ->
    bern bias >>= \tossResult478 ->
    bern bias >>= \tossResult479 ->
    bern bias >>= \tossResult480 ->
    bern bias >>= \tossResult481 ->
    bern bias >>= \tossResult482 ->
    bern bias >>= \tossResult483 ->
    bern bias >>= \tossResult484 ->
    bern bias >>= \tossResult485 ->
    bern bias >>= \tossResult486 ->
    bern bias >>= \tossResult487 ->
    bern bias >>= \tossResult488 ->
    bern bias >>= \tossResult489 ->
    bern bias >>= \tossResult490 ->
    bern bias >>= \tossResult491 ->
    bern bias >>= \tossResult492 ->
    bern bias >>= \tossResult493 ->
    bern bias >>= \tossResult494 ->
    bern bias >>= \tossResult495 ->
    bern bias >>= \tossResult496 ->
    bern bias >>= \tossResult497 ->
    bern bias >>= \tossResult498 ->
    bern bias >>= \tossResult499 ->
    dirac (pair (pair tossResult0 
                 (pair tossResult1 
                  (pair tossResult2 
                   (pair tossResult3 
                    (pair tossResult4 
                     (pair tossResult5 
                      (pair tossResult6 
                       (pair tossResult7 
                        (pair tossResult8 
                         (pair tossResult9 
                          (pair tossResult10 
                           (pair tossResult11 
                            (pair tossResult12 
                             (pair tossResult13 
                              (pair tossResult14 
                               (pair tossResult15 
                                (pair tossResult16 
                                 (pair tossResult17 
                                  (pair tossResult18 
                                   (pair tossResult19 
                                    (pair tossResult20 
                                     (pair tossResult21 
                                      (pair tossResult22 
                                       (pair tossResult23 
                                        (pair tossResult24 
                                         (pair tossResult25 
                                          (pair tossResult26 
                                           (pair tossResult27 
                                            (pair tossResult28 
                                             (pair tossResult29 
                                              (pair tossResult30 
                                               (pair tossResult31 
                                                (pair tossResult32 
                                                 (pair tossResult33 
                                                  (pair tossResult34 
                                                   (pair tossResult35 
                                                    (pair tossResult36 
                                                     (pair tossResult37 
                                                      (pair tossResult38 
                                                       (pair tossResult39 
                                                        (pair tossResult40 
                                                         (pair tossResult41 
                                                          (pair tossResult42 
                                                           (pair tossResult43 
                                                            (pair tossResult44 
                                                             (pair tossResult45 
                                                              (pair tossResult46 
                                                               (pair tossResult47 
                                                                (pair tossResult48 
                                                                 (pair tossResult49 
                                                                  (pair tossResult50 
                                                                   (pair tossResult51 
                                                                    (pair tossResult52 
                                                                     (pair tossResult53 
                                                                      (pair tossResult54 
                                                                       (pair tossResult55 
                                                                        (pair tossResult56 
                                                                         (pair tossResult57 
                                                                          (pair tossResult58 
                                                                           (pair tossResult59 
                                                                            (pair tossResult60 
                                                                             (pair tossResult61 
                                                                              (pair tossResult62 
                                                                               (pair tossResult63 
                                                                                (pair tossResult64 
                                                                                 (pair tossResult65 
                                                                                  (pair tossResult66 
                                                                                   (pair tossResult67 
                                                                                    (pair tossResult68 
                                                                                     (pair tossResult69 
                                                                                      (pair tossResult70 
                                                                                       (pair tossResult71 
                                                                                        (pair tossResult72 
                                                                                         (pair tossResult73 
                                                                                          (pair tossResult74 
                                                                                           (pair tossResult75 
                                                                                            (pair tossResult76 
                                                                                             (pair tossResult77 
                                                                                              (pair tossResult78 
                                                                                               (pair tossResult79 
                                                                                                (pair tossResult80 
                                                                                                 (pair tossResult81 
                                                                                                  (pair tossResult82 
                                                                                                   (pair tossResult83 
                                                                                                    (pair tossResult84 
                                                                                                     (pair tossResult85 
                                                                                                      (pair tossResult86 
                                                                                                       (pair tossResult87 
                                                                                                        (pair tossResult88 
                                                                                                         (pair tossResult89 
                                                                                                          (pair tossResult90 
                                                                                                           (pair tossResult91 
                                                                                                            (pair tossResult92 
                                                                                                             (pair tossResult93 
                                                                                                              (pair tossResult94 
                                                                                                               (pair tossResult95 
                                                                                                                (pair tossResult96 
                                                                                                                 (pair tossResult97 
                                                                                                                  (pair tossResult98 
                                                                                                                   (pair tossResult99 
                                                                                                                    (pair tossResult100 
                                                                                                                     (pair tossResult101 
                                                                                                                      (pair tossResult102 
                                                                                                                       (pair tossResult103 
                                                                                                                        (pair tossResult104 
                                                                                                                         (pair tossResult105 
                                                                                                                          (pair tossResult106 
                                                                                                                           (pair tossResult107 
                                                                                                                            (pair tossResult108 
                                                                                                                             (pair tossResult109 
                                                                                                                              (pair tossResult110 
                                                                                                                               (pair tossResult111 
                                                                                                                                (pair tossResult112 
                                                                                                                                 (pair tossResult113 
                                                                                                                                  (pair tossResult114 
                                                                                                                                   (pair tossResult115 
                                                                                                                                    (pair tossResult116 
                                                                                                                                     (pair tossResult117 
                                                                                                                                      (pair tossResult118 
                                                                                                                                       (pair tossResult119 
                                                                                                                                        (pair tossResult120 
                                                                                                                                         (pair tossResult121 
                                                                                                                                          (pair tossResult122 
                                                                                                                                           (pair tossResult123 
                                                                                                                                            (pair tossResult124 
                                                                                                                                             (pair tossResult125 
                                                                                                                                              (pair tossResult126 
                                                                                                                                               (pair tossResult127 
                                                                                                                                                (pair tossResult128 
                                                                                                                                                 (pair tossResult129 
                                                                                                                                                  (pair tossResult130 
                                                                                                                                                   (pair tossResult131 
                                                                                                                                                    (pair tossResult132 
                                                                                                                                                     (pair tossResult133 
                                                                                                                                                      (pair tossResult134 
                                                                                                                                                       (pair tossResult135 
                                                                                                                                                        (pair tossResult136 
                                                                                                                                                         (pair tossResult137 
                                                                                                                                                          (pair tossResult138 
                                                                                                                                                           (pair tossResult139 
                                                                                                                                                            (pair tossResult140 
                                                                                                                                                             (pair tossResult141 
                                                                                                                                                              (pair tossResult142 
                                                                                                                                                               (pair tossResult143 
                                                                                                                                                                (pair tossResult144 
                                                                                                                                                                 (pair tossResult145 
                                                                                                                                                                  (pair tossResult146 
                                                                                                                                                                   (pair tossResult147 
                                                                                                                                                                    (pair tossResult148 
                                                                                                                                                                     (pair tossResult149 
                                                                                                                                                                      (pair tossResult150 
                                                                                                                                                                       (pair tossResult151 
                                                                                                                                                                        (pair tossResult152 
                                                                                                                                                                         (pair tossResult153 
                                                                                                                                                                          (pair tossResult154 
                                                                                                                                                                           (pair tossResult155 
                                                                                                                                                                            (pair tossResult156 
                                                                                                                                                                             (pair tossResult157 
                                                                                                                                                                              (pair tossResult158 
                                                                                                                                                                               (pair tossResult159 
                                                                                                                                                                                (pair tossResult160 
                                                                                                                                                                                 (pair tossResult161 
                                                                                                                                                                                  (pair tossResult162 
                                                                                                                                                                                   (pair tossResult163 
                                                                                                                                                                                    (pair tossResult164 
                                                                                                                                                                                     (pair tossResult165 
                                                                                                                                                                                      (pair tossResult166 
                                                                                                                                                                                       (pair tossResult167 
                                                                                                                                                                                        (pair tossResult168 
                                                                                                                                                                                         (pair tossResult169 
                                                                                                                                                                                          (pair tossResult170 
                                                                                                                                                                                           (pair tossResult171 
                                                                                                                                                                                            (pair tossResult172 
                                                                                                                                                                                             (pair tossResult173 
                                                                                                                                                                                              (pair tossResult174 
                                                                                                                                                                                               (pair tossResult175 
                                                                                                                                                                                                (pair tossResult176 
                                                                                                                                                                                                 (pair tossResult177 
                                                                                                                                                                                                  (pair tossResult178 
                                                                                                                                                                                                   (pair tossResult179 
                                                                                                                                                                                                    (pair tossResult180 
                                                                                                                                                                                                     (pair tossResult181 
                                                                                                                                                                                                      (pair tossResult182 
                                                                                                                                                                                                       (pair tossResult183 
                                                                                                                                                                                                        (pair tossResult184 
                                                                                                                                                                                                         (pair tossResult185 
                                                                                                                                                                                                          (pair tossResult186 
                                                                                                                                                                                                           (pair tossResult187 
                                                                                                                                                                                                            (pair tossResult188 
                                                                                                                                                                                                             (pair tossResult189 
                                                                                                                                                                                                              (pair tossResult190 
                                                                                                                                                                                                               (pair tossResult191 
                                                                                                                                                                                                                (pair tossResult192 
                                                                                                                                                                                                                 (pair tossResult193 
                                                                                                                                                                                                                  (pair tossResult194 
                                                                                                                                                                                                                   (pair tossResult195 
                                                                                                                                                                                                                    (pair tossResult196 
                                                                                                                                                                                                                     (pair tossResult197 
                                                                                                                                                                                                                      (pair tossResult198 
                                                                                                                                                                                                                       (pair tossResult199 
                                                                                                                                                                                                                        (pair tossResult200 
                                                                                                                                                                                                                         (pair tossResult201 
                                                                                                                                                                                                                          (pair tossResult202 
                                                                                                                                                                                                                           (pair tossResult203 
                                                                                                                                                                                                                            (pair tossResult204 
                                                                                                                                                                                                                             (pair tossResult205 
                                                                                                                                                                                                                              (pair tossResult206 
                                                                                                                                                                                                                               (pair tossResult207 
                                                                                                                                                                                                                                (pair tossResult208 
                                                                                                                                                                                                                                 (pair tossResult209 
                                                                                                                                                                                                                                  (pair tossResult210 
                                                                                                                                                                                                                                   (pair tossResult211 
                                                                                                                                                                                                                                    (pair tossResult212 
                                                                                                                                                                                                                                     (pair tossResult213 
                                                                                                                                                                                                                                      (pair tossResult214 
                                                                                                                                                                                                                                       (pair tossResult215 
                                                                                                                                                                                                                                        (pair tossResult216 
                                                                                                                                                                                                                                         (pair tossResult217 
                                                                                                                                                                                                                                          (pair tossResult218 
                                                                                                                                                                                                                                           (pair tossResult219 
                                                                                                                                                                                                                                            (pair tossResult220 
                                                                                                                                                                                                                                             (pair tossResult221 
                                                                                                                                                                                                                                              (pair tossResult222 
                                                                                                                                                                                                                                               (pair tossResult223 
                                                                                                                                                                                                                                                (pair tossResult224 
                                                                                                                                                                                                                                                 (pair tossResult225 
                                                                                                                                                                                                                                                  (pair tossResult226 
                                                                                                                                                                                                                                                   (pair tossResult227 
                                                                                                                                                                                                                                                    (pair tossResult228 
                                                                                                                                                                                                                                                     (pair tossResult229 
                                                                                                                                                                                                                                                      (pair tossResult230 
                                                                                                                                                                                                                                                       (pair tossResult231 
                                                                                                                                                                                                                                                        (pair tossResult232 
                                                                                                                                                                                                                                                         (pair tossResult233 
                                                                                                                                                                                                                                                          (pair tossResult234 
                                                                                                                                                                                                                                                           (pair tossResult235 
                                                                                                                                                                                                                                                            (pair tossResult236 
                                                                                                                                                                                                                                                             (pair tossResult237 
                                                                                                                                                                                                                                                              (pair tossResult238 
                                                                                                                                                                                                                                                               (pair tossResult239 
                                                                                                                                                                                                                                                                (pair tossResult240 
                                                                                                                                                                                                                                                                 (pair tossResult241 
                                                                                                                                                                                                                                                                  (pair tossResult242 
                                                                                                                                                                                                                                                                   (pair tossResult243 
                                                                                                                                                                                                                                                                    (pair tossResult244 
                                                                                                                                                                                                                                                                     (pair tossResult245 
                                                                                                                                                                                                                                                                      (pair tossResult246 
                                                                                                                                                                                                                                                                       (pair tossResult247 
                                                                                                                                                                                                                                                                        (pair tossResult248 
                                                                                                                                                                                                                                                                         (pair tossResult249 
                                                                                                                                                                                                                                                                          (pair tossResult250 
                                                                                                                                                                                                                                                                           (pair tossResult251 
                                                                                                                                                                                                                                                                            (pair tossResult252 
                                                                                                                                                                                                                                                                             (pair tossResult253 
                                                                                                                                                                                                                                                                              (pair tossResult254 
                                                                                                                                                                                                                                                                               (pair tossResult255 
                                                                                                                                                                                                                                                                                (pair tossResult256 
                                                                                                                                                                                                                                                                                 (pair tossResult257 
                                                                                                                                                                                                                                                                                  (pair tossResult258 
                                                                                                                                                                                                                                                                                   (pair tossResult259 
                                                                                                                                                                                                                                                                                    (pair tossResult260 
                                                                                                                                                                                                                                                                                     (pair tossResult261 
                                                                                                                                                                                                                                                                                      (pair tossResult262 
                                                                                                                                                                                                                                                                                       (pair tossResult263 
                                                                                                                                                                                                                                                                                        (pair tossResult264 
                                                                                                                                                                                                                                                                                         (pair tossResult265 
                                                                                                                                                                                                                                                                                          (pair tossResult266 
                                                                                                                                                                                                                                                                                           (pair tossResult267 
                                                                                                                                                                                                                                                                                            (pair tossResult268 
                                                                                                                                                                                                                                                                                             (pair tossResult269 
                                                                                                                                                                                                                                                                                              (pair tossResult270 
                                                                                                                                                                                                                                                                                               (pair tossResult271 
                                                                                                                                                                                                                                                                                                (pair tossResult272 
                                                                                                                                                                                                                                                                                                 (pair tossResult273 
                                                                                                                                                                                                                                                                                                  (pair tossResult274 
                                                                                                                                                                                                                                                                                                   (pair tossResult275 
                                                                                                                                                                                                                                                                                                    (pair tossResult276 
                                                                                                                                                                                                                                                                                                     (pair tossResult277 
                                                                                                                                                                                                                                                                                                      (pair tossResult278 
                                                                                                                                                                                                                                                                                                       (pair tossResult279 
                                                                                                                                                                                                                                                                                                        (pair tossResult280 
                                                                                                                                                                                                                                                                                                         (pair tossResult281 
                                                                                                                                                                                                                                                                                                          (pair tossResult282 
                                                                                                                                                                                                                                                                                                           (pair tossResult283 
                                                                                                                                                                                                                                                                                                            (pair tossResult284 
                                                                                                                                                                                                                                                                                                             (pair tossResult285 
                                                                                                                                                                                                                                                                                                              (pair tossResult286 
                                                                                                                                                                                                                                                                                                               (pair tossResult287 
                                                                                                                                                                                                                                                                                                                (pair tossResult288 
                                                                                                                                                                                                                                                                                                                 (pair tossResult289 
                                                                                                                                                                                                                                                                                                                  (pair tossResult290 
                                                                                                                                                                                                                                                                                                                   (pair tossResult291 
                                                                                                                                                                                                                                                                                                                    (pair tossResult292 
                                                                                                                                                                                                                                                                                                                     (pair tossResult293 
                                                                                                                                                                                                                                                                                                                      (pair tossResult294 
                                                                                                                                                                                                                                                                                                                       (pair tossResult295 
                                                                                                                                                                                                                                                                                                                        (pair tossResult296 
                                                                                                                                                                                                                                                                                                                         (pair tossResult297 
                                                                                                                                                                                                                                                                                                                          (pair tossResult298 
                                                                                                                                                                                                                                                                                                                           (pair tossResult299 
                                                                                                                                                                                                                                                                                                                            (pair tossResult300 
                                                                                                                                                                                                                                                                                                                             (pair tossResult301 
                                                                                                                                                                                                                                                                                                                              (pair tossResult302 
                                                                                                                                                                                                                                                                                                                               (pair tossResult303 
                                                                                                                                                                                                                                                                                                                                (pair tossResult304 
                                                                                                                                                                                                                                                                                                                                 (pair tossResult305 
                                                                                                                                                                                                                                                                                                                                  (pair tossResult306 
                                                                                                                                                                                                                                                                                                                                   (pair tossResult307 
                                                                                                                                                                                                                                                                                                                                    (pair tossResult308 
                                                                                                                                                                                                                                                                                                                                     (pair tossResult309 
                                                                                                                                                                                                                                                                                                                                      (pair tossResult310 
                                                                                                                                                                                                                                                                                                                                       (pair tossResult311 
                                                                                                                                                                                                                                                                                                                                        (pair tossResult312 
                                                                                                                                                                                                                                                                                                                                         (pair tossResult313 
                                                                                                                                                                                                                                                                                                                                          (pair tossResult314 
                                                                                                                                                                                                                                                                                                                                           (pair tossResult315 
                                                                                                                                                                                                                                                                                                                                            (pair tossResult316 
                                                                                                                                                                                                                                                                                                                                             (pair tossResult317 
                                                                                                                                                                                                                                                                                                                                              (pair tossResult318 
                                                                                                                                                                                                                                                                                                                                               (pair tossResult319 
                                                                                                                                                                                                                                                                                                                                                (pair tossResult320 
                                                                                                                                                                                                                                                                                                                                                 (pair tossResult321 
                                                                                                                                                                                                                                                                                                                                                  (pair tossResult322 
                                                                                                                                                                                                                                                                                                                                                   (pair tossResult323 
                                                                                                                                                                                                                                                                                                                                                    (pair tossResult324 
                                                                                                                                                                                                                                                                                                                                                     (pair tossResult325 
                                                                                                                                                                                                                                                                                                                                                      (pair tossResult326 
                                                                                                                                                                                                                                                                                                                                                       (pair tossResult327 
                                                                                                                                                                                                                                                                                                                                                        (pair tossResult328 
                                                                                                                                                                                                                                                                                                                                                         (pair tossResult329 
                                                                                                                                                                                                                                                                                                                                                          (pair tossResult330 
                                                                                                                                                                                                                                                                                                                                                           (pair tossResult331 
                                                                                                                                                                                                                                                                                                                                                            (pair tossResult332 
                                                                                                                                                                                                                                                                                                                                                             (pair tossResult333 
                                                                                                                                                                                                                                                                                                                                                              (pair tossResult334 
                                                                                                                                                                                                                                                                                                                                                               (pair tossResult335 
                                                                                                                                                                                                                                                                                                                                                                (pair tossResult336 
                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult337 
                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult338 
                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult339 
                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult340 
                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult341 
                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult342 
                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult343 
                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult344 
                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult345 
                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult346 
                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult347 
                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult348 
                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult349 
                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult350 
                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult351 
                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult352 
                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult353 
                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult354 
                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult355 
                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult356 
                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult357 
                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult358 
                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult359 
                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult360 
                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult361 
                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult362 
                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult363 
                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult364 
                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult365 
                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult366 
                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult367 
                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult368 
                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult369 
                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult370 
                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult371 
                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult372 
                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult373 
                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult374 
                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult375 
                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult376 
                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult377 
                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult378 
                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult379 
                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult380 
                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult381 
                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult382 
                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult383 
                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult384 
                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult385 
                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult386 
                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult387 
                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult388 
                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult389 
                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult390 
                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult391 
                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult392 
                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult393 
                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult394 
                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult395 
                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult396 
                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult397 
                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult398 
                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult399 
                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult400 
                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult401 
                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult402 
                                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult403 
                                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult404 
                                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult405 
                                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult406 
                                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult407 
                                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult408 
                                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult409 
                                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult410 
                                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult411 
                                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult412 
                                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult413 
                                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult414 
                                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult415 
                                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult416 
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult417 
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult418 
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult419 
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult420 
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult421 
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult422 
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult423 
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult424 
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult425 
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult426 
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult427 
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult428 
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult429 
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult430 
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult431 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult432 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult433 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult434 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult435 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult436 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult437 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult438 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult439 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult440 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult441 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult442 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult443 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult444 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult445 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult446 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult447 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult448 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult449 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult450 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult451 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult452 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult453 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult454 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult455 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult456 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult457 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult458 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult459 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult460 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult461 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult462 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult463 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult464 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult465 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult466 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult467 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult468 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult469 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult470 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult471 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult472 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult473 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult474 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult475 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult476 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult477 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult478 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult479 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult480 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult481 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult482 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (pair tossResult483 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pair tossResult484 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (pair tossResult485 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pair tossResult486 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (pair tossResult487 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pair tossResult488 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (pair tossResult489 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (pair tossResult490 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (pair tossResult491 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pair tossResult492 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (pair tossResult493 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (pair tossResult494 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (pair tossResult495 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pair tossResult496 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (pair tossResult497 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pair tossResult498 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   tossResult499)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           bias)

main :: IO ()
main = print (length (disintegrate coinBias))

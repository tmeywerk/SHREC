(set-logic QF_LRA)
(declare-fun r0 () Real)
(declare-fun b0 () Bool)
(declare-fun r1 () Real)
(declare-fun b3 () Bool)
(declare-fun r2 () Real)
(declare-fun b2 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 2222078044393861 2251799813685248)) r3))) (let ((.def_1 (* (/ 6965500260678811 9007199254740992) r2))) (let ((.def_2 (* (/ 6354759890413765 9007199254740992) r1))) (let ((.def_3 (* (/ 2587793150355411 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 2954358813392217 9007199254740992)))) (let ((.def_6 (* (/ 8432852144515623 9007199254740992) r3))) (let ((.def_7 (* (/ 1375081932189963 9007199254740992) r2))) (let ((.def_8 (* (- (/ 8266482192743993 9007199254740992)) r1))) (let ((.def_9 (* (- (/ 1087026171707091 4503599627370496)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 241688079487607 1125899906842624))))) (let ((.def_12 (not b2))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 2074289340538001 2251799813685248)) r3))) (let ((.def_15 (* (- (/ 3007302143424957 4503599627370496)) r2))) (let ((.def_16 (* (- (/ 907875426709565 1125899906842624)) r1))) (let ((.def_17 (* (/ 3085868059822587 4503599627370496) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 1928063023965899 2251799813685248))))) (let ((.def_20 (* (- (/ 6875282885178109 9007199254740992)) r3))) (let ((.def_21 (* (- (/ 2351654360662235 4503599627370496)) r2))) (let ((.def_22 (* (/ 1715689866460509 2251799813685248) r1))) (let ((.def_23 (* (- (/ 605361855891723 562949953421312)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (- (/ 645457169628047 562949953421312))))) (let ((.def_26 (or b3 .def_25 .def_19))) (let ((.def_27 (* (/ 4576962042443939 4503599627370496) r3))) (let ((.def_28 (* (- (/ 2149294066587975 2251799813685248)) r2))) (let ((.def_29 (* (/ 29583802195357 1125899906842624) r1))) (let ((.def_30 (* (- (/ 1483666388049281 2251799813685248)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (- (/ 53610006609595 2251799813685248))))) (let ((.def_33 (* (- (/ 322924558124613 281474976710656)) r3))) (let ((.def_34 (* (- (/ 7878138134316451 4503599627370496)) r2))) (let ((.def_35 (* (/ 6168746599539903 2251799813685248) r1))) (let ((.def_36 (* (- (/ 6623411780780167 9007199254740992)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 3698145719889107 4503599627370496))))) (let ((.def_39 (or b0 .def_38 .def_32))) (let ((.def_40 (* (/ 32250807910847 4503599627370496) r3))) (let ((.def_41 (* (/ 2069949573260671 1125899906842624) r2))) (let ((.def_42 (* (- (/ 564696456218369 562949953421312)) r1))) (let ((.def_43 (* (- (/ 3979586638120863 4503599627370496)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (- (/ 186618473615881 1125899906842624))))) (let ((.def_46 (* (- (/ 7831677031006975 9007199254740992)) r3))) (let ((.def_47 (* (- (/ 1490268286927351 9007199254740992)) r2))) (let ((.def_48 (* (/ 5144948713422839 4503599627370496) r1))) (let ((.def_49 (* (/ 641270690068723 2251799813685248) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 264958329065477 4503599627370496)))) (let ((.def_52 (or b3 .def_51 .def_45))) (let ((.def_53 (and .def_52 .def_39 .def_26 .def_13))) .def_53)))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
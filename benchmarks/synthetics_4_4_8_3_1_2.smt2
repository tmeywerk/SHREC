(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b2 () Bool)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (/ 4160638124823983 4503599627370496) r3))) (let ((.def_1 (* (/ 3211501868090765 4503599627370496) r2))) (let ((.def_2 (* (- (/ 3260098736759277 9007199254740992)) r1))) (let ((.def_3 (* (/ 3582763361176655 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 323411969676621 281474976710656)))) (let ((.def_6 (not b1))) (let ((.def_7 (or .def_6 b0 .def_5))) (let ((.def_8 (* (/ 56717048742467 140737488355328) r3))) (let ((.def_9 (* (/ 701002204696951 1125899906842624) r2))) (let ((.def_10 (* (- (/ 8174116474312301 9007199254740992)) r1))) (let ((.def_11 (* (/ 432953971710451 2251799813685248) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 917668719174009 4503599627370496)))) (let ((.def_14 (or b3 .def_6 .def_13))) (let ((.def_15 (* (- (/ 1788763907007121 2251799813685248)) r3))) (let ((.def_16 (* (/ 536961576631737 4503599627370496) r2))) (let ((.def_17 (* (- (/ 461228734923275 9007199254740992)) r1))) (let ((.def_18 (* (- (/ 906711007741705 2251799813685248)) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (- (/ 3129252563471807 4503599627370496))))) (let ((.def_21 (or b0 b2 .def_20))) (let ((.def_22 (* (- (/ 884035973338483 9007199254740992)) r3))) (let ((.def_23 (* (- (/ 8035025880645573 9007199254740992)) r2))) (let ((.def_24 (* (- (/ 6678939164154879 9007199254740992)) r1))) (let ((.def_25 (* (- (/ 3769271526579771 2251799813685248)) r0))) (let ((.def_26 (+ .def_25 .def_24 .def_23 .def_22))) (let ((.def_27 (<= .def_26 (- (/ 6112848336939851 4503599627370496))))) (let ((.def_28 (or b3 b0 .def_27))) (let ((.def_29 (* (- (/ 2611398229400875 4503599627370496)) r3))) (let ((.def_30 (* (/ 3721931186386759 4503599627370496) r2))) (let ((.def_31 (* (/ 191647240552895 281474976710656) r1))) (let ((.def_32 (* (/ 7570387734021 1125899906842624) r0))) (let ((.def_33 (+ .def_32 .def_31 .def_30 .def_29))) (let ((.def_34 (<= .def_33 (/ 1420705422485259 2251799813685248)))) (let ((.def_35 (not b3))) (let ((.def_36 (or .def_35 b1 .def_34))) (let ((.def_37 (* (- (/ 3870096359458063 4503599627370496)) r3))) (let ((.def_38 (* (/ 22546914217489 9007199254740992) r2))) (let ((.def_39 (* (/ 2093513633850765 2251799813685248) r1))) (let ((.def_40 (* (/ 1069906667234831 4503599627370496) r0))) (let ((.def_41 (+ .def_40 .def_39 .def_38 .def_37))) (let ((.def_42 (<= .def_41 (/ 3960155860024083 9007199254740992)))) (let ((.def_43 (or b1 b2 .def_42))) (let ((.def_44 (* (/ 2827867663881131 4503599627370496) r3))) (let ((.def_45 (* (/ 3066030550996089 2251799813685248) r2))) (let ((.def_46 (* (/ 970447057314031 4503599627370496) r1))) (let ((.def_47 (* (- (/ 3405049526471195 2251799813685248)) r0))) (let ((.def_48 (+ .def_47 .def_46 .def_45 .def_44))) (let ((.def_49 (<= .def_48 (/ 3608086669714229 4503599627370496)))) (let ((.def_50 (or b2 .def_6 .def_49))) (let ((.def_51 (* (/ 3740041460457317 2251799813685248) r3))) (let ((.def_52 (* (- (/ 4071299054287743 2251799813685248)) r2))) (let ((.def_53 (* (- (/ 3654266002747409 9007199254740992)) r1))) (let ((.def_54 (* (- (/ 130147976653353 4503599627370496)) r0))) (let ((.def_55 (+ .def_54 .def_53 .def_52 .def_51))) (let ((.def_56 (<= .def_55 (/ 2889222622614591 9007199254740992)))) (let ((.def_57 (or b2 .def_35 .def_56))) (let ((.def_58 (and .def_57 .def_50 .def_43 .def_36 .def_28 .def_21 .def_14 .def_7))) .def_58))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)

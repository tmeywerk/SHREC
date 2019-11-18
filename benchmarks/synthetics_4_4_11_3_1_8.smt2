(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (/ 2994197037936111 9007199254740992) r3))) (let ((.def_1 (* (/ 2512568553336201 2251799813685248) r2))) (let ((.def_2 (* (- (/ 6710292904462409 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 2814633807803391 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 35439778694259 2251799813685248))))) (let ((.def_6 (not b0))) (let ((.def_7 (not b1))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (/ 1084760639759215 2251799813685248) r3))) (let ((.def_10 (* (/ 3085117751352137 4503599627370496) r2))) (let ((.def_11 (* (- (/ 5434766979840501 9007199254740992)) r1))) (let ((.def_12 (* (- (/ 4761758749937723 9007199254740992)) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (/ 37571825612015 281474976710656)))) (let ((.def_15 (or .def_6 b2 .def_14))) (let ((.def_16 (* (- (/ 248626728273169 70368744177664)) r3))) (let ((.def_17 (* (- (/ 67105741725695 1125899906842624)) r2))) (let ((.def_18 (* (- (/ 779462548632599 4503599627370496)) r1))) (let ((.def_19 (* (/ 459025556690703 1125899906842624) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 125046973064101 281474976710656))))) (let ((.def_22 (not b2))) (let ((.def_23 (or b1 .def_22 .def_21))) (let ((.def_24 (* (/ 1028057883859179 2251799813685248) r3))) (let ((.def_25 (* (- (/ 4858777677979453 9007199254740992)) r2))) (let ((.def_26 (* (- (/ 1303217386292921 4503599627370496)) r1))) (let ((.def_27 (* (- (/ 1283422798805661 2251799813685248)) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (- (/ 79728023680437 281474976710656))))) (let ((.def_30 (or b3 .def_6 .def_29))) (let ((.def_31 (* (- (/ 4379248556746483 2251799813685248)) r3))) (let ((.def_32 (* (- (/ 182477727032819 9007199254740992)) r2))) (let ((.def_33 (* (- (/ 3222013262304347 2251799813685248)) r1))) (let ((.def_34 (* (/ 3695875259526643 9007199254740992) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 2576355544894795 2251799813685248))))) (let ((.def_37 (or .def_7 .def_22 .def_36))) (let ((.def_38 (* (- (/ 1888732216079351 1125899906842624)) r3))) (let ((.def_39 (* (- (/ 1940297789938611 2251799813685248)) r2))) (let ((.def_40 (* (- (/ 24552415008541 2251799813685248)) r1))) (let ((.def_41 (* (/ 3927927799627155 4503599627370496) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 3494342604402081 4503599627370496))))) (let ((.def_44 (or b3 b2 .def_43))) (let ((.def_45 (* (- (/ 6495264960010849 4503599627370496)) r3))) (let ((.def_46 (* (/ 1112603315465337 4503599627370496) r2))) (let ((.def_47 (* (- (/ 239696917282141 1125899906842624)) r1))) (let ((.def_48 (* (- (/ 1789932450575423 4503599627370496)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 2656860708347531 4503599627370496))))) (let ((.def_51 (or b3 b2 .def_50))) (let ((.def_52 (* (- (/ 2506409250910569 1125899906842624)) r3))) (let ((.def_53 (* (/ 217592487658167 4503599627370496) r2))) (let ((.def_54 (* (- (/ 675793863864193 4503599627370496)) r1))) (let ((.def_55 (* (/ 7647962658474147 9007199254740992) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 228729567086221 9007199254740992)))) (let ((.def_58 (or .def_22 .def_7 .def_57))) (let ((.def_59 (* (- (/ 1116368286423101 4503599627370496)) r3))) (let ((.def_60 (* (/ 2668944897128125 9007199254740992) r2))) (let ((.def_61 (* (/ 2133671026937261 2251799813685248) r1))) (let ((.def_62 (* (- (/ 2036354994303905 2251799813685248)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 960457405812241 4503599627370496)))) (let ((.def_65 (not b3))) (let ((.def_66 (or b2 .def_65 .def_64))) (let ((.def_67 (* (- (/ 592244990163305 1125899906842624)) r3))) (let ((.def_68 (* (/ 1226340012096137 4503599627370496) r2))) (let ((.def_69 (* (- (/ 2864163704345579 2251799813685248)) r1))) (let ((.def_70 (* (- (/ 5403794253082185 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 3069191581052661 2251799813685248))))) (let ((.def_73 (or b2 b1 .def_72))) (let ((.def_74 (* (- (/ 1072011248267263 2251799813685248)) r3))) (let ((.def_75 (* (- (/ 876341386117853 562949953421312)) r2))) (let ((.def_76 (* (/ 127658414583701 1125899906842624) r1))) (let ((.def_77 (* (- (/ 3708419098643683 2251799813685248)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 5220897867142065 4503599627370496))))) (let ((.def_80 (or .def_65 b2 .def_79))) (let ((.def_81 (and .def_80 .def_73 .def_66 .def_58 .def_51 .def_44 .def_37 .def_30 .def_23 .def_15 .def_8))) .def_81)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)

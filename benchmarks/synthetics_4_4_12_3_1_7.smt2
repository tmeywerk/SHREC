(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (/ 2369884751539251 4503599627370496) r3))) (let ((.def_1 (* (- (/ 3844272210902519 4503599627370496)) r2))) (let ((.def_2 (* (/ 1694694933992831 1125899906842624) r1))) (let ((.def_3 (* (- (/ 1564513548548855 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 81775139100163 140737488355328)))) (let ((.def_6 (not b0))) (let ((.def_7 (or .def_6 b3 .def_5))) (let ((.def_8 (* (- (/ 369145903578181 281474976710656)) r3))) (let ((.def_9 (* (/ 1321796128191295 4503599627370496) r2))) (let ((.def_10 (* (- (/ 273994060234759 281474976710656)) r1))) (let ((.def_11 (* (/ 1634930700140569 4503599627370496) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 1876186356812411 4503599627370496))))) (let ((.def_14 (not b3))) (let ((.def_15 (or .def_14 b1 .def_13))) (let ((.def_16 (* (/ 5330747142628657 4503599627370496) r3))) (let ((.def_17 (* (- (/ 3473627733308533 2251799813685248)) r2))) (let ((.def_18 (* (/ 5527990676967397 9007199254740992) r1))) (let ((.def_19 (* (- (/ 748124851507921 4503599627370496)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (/ 2665335408165205 9007199254740992)))) (let ((.def_22 (or b2 .def_14 .def_21))) (let ((.def_23 (* (- (/ 1768520182619821 9007199254740992)) r3))) (let ((.def_24 (* (- (/ 5184456068890099 9007199254740992)) r2))) (let ((.def_25 (* (- (/ 2428991644140991 4503599627370496)) r1))) (let ((.def_26 (* (- (/ 932132847309617 2251799813685248)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 3447071015186341 4503599627370496))))) (let ((.def_29 (not b1))) (let ((.def_30 (or .def_29 .def_14 .def_28))) (let ((.def_31 (* (/ 880601119874251 2251799813685248) r3))) (let ((.def_32 (* (/ 2584841972289049 4503599627370496) r2))) (let ((.def_33 (* (/ 2994636016156095 4503599627370496) r1))) (let ((.def_34 (* (- (/ 2025867092543933 4503599627370496)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 3881379864945415 4503599627370496)))) (let ((.def_37 (or b1 b0 .def_36))) (let ((.def_38 (* (/ 1997230337401291 2251799813685248) r3))) (let ((.def_39 (* (- (/ 4144574619609529 4503599627370496)) r2))) (let ((.def_40 (* (- (/ 837261425671845 9007199254740992)) r1))) (let ((.def_41 (* (- (/ 2367636861441031 2251799813685248)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 1144777623190609 4503599627370496))))) (let ((.def_44 (not b2))) (let ((.def_45 (or .def_44 .def_6 .def_43))) (let ((.def_46 (* (- (/ 367938372967383 281474976710656)) r3))) (let ((.def_47 (* (- (/ 242365596463351 562949953421312)) r2))) (let ((.def_48 (* (/ 167780259581687 562949953421312) r1))) (let ((.def_49 (* (- (/ 369714701231941 1125899906842624)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 568669936328035 1125899906842624))))) (let ((.def_52 (or .def_6 .def_44 .def_51))) (let ((.def_53 (* (- (/ 14296869656659 8796093022208)) r3))) (let ((.def_54 (* (- (/ 5011016651259143 2251799813685248)) r2))) (let ((.def_55 (* (/ 2441166568208359 1125899906842624) r1))) (let ((.def_56 (* (/ 847172617875131 4503599627370496) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 460292456825721 4503599627370496)))) (let ((.def_59 (or .def_14 b1 .def_58))) (let ((.def_60 (* (- (/ 5608217673356013 4503599627370496)) r3))) (let ((.def_61 (* (- (/ 3844557544472733 2251799813685248)) r2))) (let ((.def_62 (* (- (/ 719106587262369 9007199254740992)) r1))) (let ((.def_63 (* (/ 863326617497037 562949953421312) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 459586402807921 9007199254740992))))) (let ((.def_66 (or .def_14 b2 .def_65))) (let ((.def_67 (* (/ 7826792366649273 9007199254740992) r3))) (let ((.def_68 (* (- (/ 8355073819621071 9007199254740992)) r2))) (let ((.def_69 (* (- (/ 8585553076092809 2251799813685248)) r1))) (let ((.def_70 (* (/ 43110195350901 281474976710656) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 6444695157689403 9007199254740992))))) (let ((.def_73 (or .def_29 .def_6 .def_72))) (let ((.def_74 (* (- (/ 236765308818665 2251799813685248)) r3))) (let ((.def_75 (* (/ 3235813821179361 9007199254740992) r2))) (let ((.def_76 (* (- (/ 4023554242243181 2251799813685248)) r1))) (let ((.def_77 (* (- (/ 1853343047062357 4503599627370496)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 1899234416836759 4503599627370496))))) (let ((.def_80 (or b3 .def_44 .def_79))) (let ((.def_81 (* (- (/ 196073708485511 562949953421312)) r3))) (let ((.def_82 (* (- (/ 2511653326484359 9007199254740992)) r2))) (let ((.def_83 (* (- (/ 4937080866250115 9007199254740992)) r1))) (let ((.def_84 (* (/ 4677514038221257 4503599627370496) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 714042371646353 2251799813685248)))) (let ((.def_87 (or b0 .def_29 .def_86))) (let ((.def_88 (and .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_37 .def_30 .def_22 .def_15 .def_7))) .def_88))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
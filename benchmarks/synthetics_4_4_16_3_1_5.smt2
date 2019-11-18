(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 1085277012672393 1125899906842624)) r3))) (let ((.def_1 (* (- (/ 5552865271120939 9007199254740992)) r2))) (let ((.def_2 (* (- (/ 1861208332906699 4503599627370496)) r1))) (let ((.def_3 (* (/ 87290319207047 562949953421312) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2944491713256011 4503599627370496))))) (let ((.def_6 (not b3))) (let ((.def_7 (not b0))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (/ 3308261254029495 9007199254740992) r3))) (let ((.def_10 (* (- (/ 4529115737581423 4503599627370496)) r2))) (let ((.def_11 (* (/ 444454719046197 562949953421312) r1))) (let ((.def_12 (* (- (/ 2505865499109731 4503599627370496)) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (/ 846494460833361 4503599627370496)))) (let ((.def_15 (or b3 b1 .def_14))) (let ((.def_16 (* (/ 4414056457121035 9007199254740992) r3))) (let ((.def_17 (* (- (/ 848905025123367 9007199254740992)) r2))) (let ((.def_18 (* (- (/ 3609556176384061 2251799813685248)) r1))) (let ((.def_19 (* (- (/ 7037597934549239 9007199254740992)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 275747311067405 562949953421312))))) (let ((.def_22 (not b2))) (let ((.def_23 (or .def_22 .def_7 .def_21))) (let ((.def_24 (* (- (/ 871919363708857 1125899906842624)) r3))) (let ((.def_25 (* (- (/ 565154908724603 1125899906842624)) r2))) (let ((.def_26 (* (- (/ 108233810020655 562949953421312)) r1))) (let ((.def_27 (* (- (/ 743560926006745 4503599627370496)) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (- (/ 2533701433576143 4503599627370496))))) (let ((.def_30 (or b0 b2 .def_29))) (let ((.def_31 (* (- (/ 645170363287217 2251799813685248)) r3))) (let ((.def_32 (* (/ 1203896738674507 4503599627370496) r2))) (let ((.def_33 (* (/ 2446108210069529 4503599627370496) r1))) (let ((.def_34 (* (- (/ 6588479678165629 9007199254740992)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 787290952517631 4503599627370496)))) (let ((.def_37 (not b1))) (let ((.def_38 (or .def_37 .def_7 .def_36))) (let ((.def_39 (* (- (/ 2500871062702381 1125899906842624)) r3))) (let ((.def_40 (* (/ 3062916129287899 9007199254740992) r2))) (let ((.def_41 (* (/ 2626860525929227 2251799813685248) r1))) (let ((.def_42 (* (- (/ 4955744099817563 9007199254740992)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 69197669907591 4503599627370496)))) (let ((.def_45 (or .def_6 .def_22 .def_44))) (let ((.def_46 (* (- (/ 5494749353917593 2251799813685248)) r3))) (let ((.def_47 (* (- (/ 2665844413121951 4503599627370496)) r2))) (let ((.def_48 (* (- (/ 1299989441273011 9007199254740992)) r1))) (let ((.def_49 (* (- (/ 1888240421466169 2251799813685248)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 1461292298185499 1125899906842624))))) (let ((.def_52 (or b1 .def_6 .def_51))) (let ((.def_53 (* (- (/ 3070031091262203 2251799813685248)) r3))) (let ((.def_54 (* (- (/ 7097716088481645 9007199254740992)) r2))) (let ((.def_55 (* (- (/ 85606172555469 4503599627370496)) r1))) (let ((.def_56 (* (- (/ 4335212951647299 4503599627370496)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 3562069302469159 4503599627370496))))) (let ((.def_59 (or .def_7 b2 .def_58))) (let ((.def_60 (* (/ 963755405765159 2251799813685248) r3))) (let ((.def_61 (* (- (/ 1243513515148749 4503599627370496)) r2))) (let ((.def_62 (* (- (/ 633072667220477 2251799813685248)) r1))) (let ((.def_63 (* (/ 2136271670406173 4503599627370496) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 3346792048036525 9007199254740992)))) (let ((.def_66 (or .def_37 .def_22 .def_65))) (let ((.def_67 (* (- (/ 4374082460772573 4503599627370496)) r3))) (let ((.def_68 (* (- (/ 1410529391687583 4503599627370496)) r2))) (let ((.def_69 (* (/ 1336039534722569 1125899906842624) r1))) (let ((.def_70 (* (- (/ 886359414361565 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 1618923506313679 9007199254740992)))) (let ((.def_73 (or .def_22 b0 .def_72))) (let ((.def_74 (* (/ 3170102809108573 4503599627370496) r3))) (let ((.def_75 (* (/ 4557362761373189 9007199254740992) r2))) (let ((.def_76 (* (- (/ 972739461047023 1125899906842624)) r1))) (let ((.def_77 (* (- (/ 910999627452581 2251799813685248)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 1748461059792277 4503599627370496)))) (let ((.def_80 (or b0 .def_37 .def_79))) (let ((.def_81 (* (/ 4904098687084675 4503599627370496) r3))) (let ((.def_82 (* (- (/ 1073554979851115 1125899906842624)) r2))) (let ((.def_83 (* (/ 470742533918313 4503599627370496) r1))) (let ((.def_84 (* (/ 3657620333065393 9007199254740992) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 6338592264075901 9007199254740992)))) (let ((.def_87 (or b2 b0 .def_86))) (let ((.def_88 (* (/ 1202521482041577 2251799813685248) r3))) (let ((.def_89 (* (/ 1606692638945083 1125899906842624) r2))) (let ((.def_90 (* (- (/ 883697562355451 4503599627370496)) r1))) (let ((.def_91 (* (- (/ 1917389553449967 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (/ 5444833394799287 4503599627370496)))) (let ((.def_94 (or b1 b2 .def_93))) (let ((.def_95 (* (- (/ 1731332022449647 1125899906842624)) r3))) (let ((.def_96 (* (- (/ 94537742683719 70368744177664)) r2))) (let ((.def_97 (* (/ 1622821699692731 4503599627370496) r1))) (let ((.def_98 (* (/ 4178047252557335 9007199254740992) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (- (/ 3020451716339575 9007199254740992))))) (let ((.def_101 (or b1 b0 .def_100))) (let ((.def_102 (* (/ 1571107249251967 4503599627370496) r3))) (let ((.def_103 (* (- (/ 5796422705093719 4503599627370496)) r2))) (let ((.def_104 (* (- (/ 1510809852804355 2251799813685248)) r1))) (let ((.def_105 (* (- (/ 713872966405915 2251799813685248)) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (- (/ 1691637489878961 4503599627370496))))) (let ((.def_108 (or b1 .def_6 .def_107))) (let ((.def_109 (* (/ 795777628766565 1125899906842624) r3))) (let ((.def_110 (* (- (/ 3684165180809127 2251799813685248)) r2))) (let ((.def_111 (* (/ 2866655263731749 9007199254740992) r1))) (let ((.def_112 (* (- (/ 70586854021327 2251799813685248)) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 564766085833405 2251799813685248)))) (let ((.def_115 (or b3 .def_37 .def_114))) (let ((.def_116 (and .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_38 .def_30 .def_23 .def_15 .def_8))) .def_116))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)

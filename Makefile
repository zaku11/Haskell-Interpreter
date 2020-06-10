all:
	happy -gca ParJanŻakGramatyka.y
	alex -g LexJanŻakGramatyka.x
	ghc --make TestJanŻakGramatyka.hs -o interpreter

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocJanŻakGramatyka.* LexJanŻakGramatyka.* ParJanŻakGramatyka.* LayoutJanŻakGramatyka.* SkelJanŻakGramatyka.* PrintJanŻakGramatyka.* TestJanŻakGramatyka.* AbsJanŻakGramatyka.* TestJanŻakGramatyka ErrM.* SharedString.* ComposOp.* Jan_Żak_gramatyka.dtd XMLJanŻakGramatyka.* Makefile*
	

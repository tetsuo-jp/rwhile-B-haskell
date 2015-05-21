all: ri

warn: Main.hs
	ghc -Wall -fno-warn-unused-do-bind --make Main.hs

ri: Ast.hs Invert.hs Parser.hs Trans.hs Eval.hs ToData.hs Main.hs
	ghc -o $@ --make Main.hs
	# ghc --make Main.hs -with-rtsopts="-H128m -K64m"

clean:
	-rm -f ri
	-rm -f *.hi *.o
	-rm -f Main

test:
	./ri ../examples/reverse.rwhile ../examples/list_abc.val
	./ri --to RCoreData ../examples/reverse.rwhile
	./ri ../examples/rint.rwhile ../examples/reverse_and_list_abc.val
	./ri ../examples/map_inc.rwhile ../examples/010.rcore_val
	./ri ../examples/t10.rwhilerm ../examples/list_abc.val
	./ri ../examples/unary2binary.rwhilewm ../examples/nil^10.val
	./ri ../examples/postorder_inorder.rwhile ../examples/piorder_input01.rcore_val
	./ri ../examples/postorder_inorder.rwhile ../examples/piorder_input02.rcore_val
	./ri ../examples/postorder_inorder.rwhile ../examples/piorder_input03.rcore_val
	./ri ../examples/postorder_inorder.rwhile ../examples/piorder_input04.rcore_val
	./ri ../examples/postorder_inorder.rwhile ../examples/piorder_input05.rcore_val
	./ri ../examples/piorder.rwhile ../examples/piorder_input01.rcore_val
	./ri ../examples/piorder.rwhile ../examples/piorder_input02.rcore_val
	./ri ../examples/piorder.rwhile ../examples/piorder_input03.rcore_val
	./ri ../examples/piorder.rwhile ../examples/piorder_input04.rcore_val
	./ri ../examples/piorder.rwhile ../examples/piorder_input05.rcore_val
	./ri ../examples/map_inc.rwhile ../examples/000.rcore_val
	./ri ../examples/map_inc.rwhile ../examples/001.rcore_val
	./ri ../examples/t01.rcore ../examples/nil.val
	./ri ../examples/t02.rcore ../examples/nil.val
	./ri ../examples/t03.rcore ../examples/nil.val
	./ri ../examples/t04.rcore ../examples/nil.val
	./ri ../examples/t05.rcore ../examples/nil.val
	./ri ../examples/t06.rcore ../examples/true.val
	./ri ../examples/t08.rcore ../examples/nil.val
	./ri ../examples/t09.rcore ../examples/nil.val
	./ri ../examples/add.rwhilewm ../examples/nil.val

cd /Users/leroux/Documents/PROGRAMMATION/LEAN/LEAN_TRAVAIL/dEAduction-lean
echo "Copy lean_src..."
cp -v src/lean_src_deaduction_synchro/* ../dEAduction/src/deaduction/lean_src
echo "Copy courses (recursively)..."
cp -v -r src/exercises_deaduction_synchro/* ../dEAduction/src/deaduction/share/courses
echo "Copy exercises for testing -> tests..."
cp -v snippets/new_exercises_for_testing_deaduction_synchro/* ../dEAduction/tests/lean_files/courses/
echo "Copy test files -> tests..."
cp -v autotest_deaduction_synchro/autotest_exercises/* ../dEAduction/tests/autotest_buttons

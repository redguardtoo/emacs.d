import unittest
import tempfile
import shutil
import os
import mock

from elpy import refactor
from textwrap import dedent


class RefactorTestCase(unittest.TestCase):
    def setUp(self):
        self.project_root = tempfile.mkdtemp(prefix="test-refactor-root")
        self.addCleanup(shutil.rmtree, self.project_root,
                        ignore_errors=True)

    def create_file(self, name, contents=""):
        filename = os.path.join(self.project_root, name)
        contents = dedent(contents)
        offset = contents.find("_|_")
        if offset > -1:
            contents = contents[:offset] + contents[offset + 3:]
        with open(filename, "w") as f:
            f.write(contents)
        return filename, offset

    def assertSourceEqual(self, first, second, msg=None):
        """Fail if the two objects are unequal, ignoring indentation."""
        self.assertEqual(dedent(first), dedent(second), msg=msg)


class TestGetRefactorOptions(RefactorTestCase):
    def test_should_only_return_importsmodule_if_not_on_symbol(self):
        filename, offset = self.create_file("foo.py",
                                            """\
                                            import foo
                                            _|_""")
        ref = refactor.Refactor(self.project_root, filename)
        options = ref.get_refactor_options(offset)
        self.assertTrue(all(opt['category'] in ('Imports',
                                                'Module')
                            for opt in options))
        filename, offset = self.create_file("foo.py",
                                            """\
                                            _|_
                                            import foo""")
        ref = refactor.Refactor(self.project_root, filename)
        options = ref.get_refactor_options(offset)
        self.assertTrue(all(opt['category'] in ('Imports',
                                                'Module')
                            for opt in options))

    def test_should_return_all_if_on_symbol(self):
        filename, offset = self.create_file("foo.py",
                                            "import _|_foo")
        ref = refactor.Refactor(self.project_root, filename)
        options = ref.get_refactor_options(offset)
        self.assertTrue(all(opt['category'] in ('Imports',
                                                'Method',
                                                'Module',
                                                'Symbol')
                            for opt in options))

    def test_should_return_only_region_if_endoffset(self):
        filename, offset = self.create_file("foo.py",
                                            "import foo")
        ref = refactor.Refactor(self.project_root, filename)
        options = ref.get_refactor_options(offset, 5)
        self.assertTrue(all(opt['category'] == 'Region'
                            for opt in options))

    @unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
    def test_should_treat_from_import_special(self):
        filename, offset = self.create_file("foo.py",
                                            """\
                                            import foo
                                            _|_""")
        ref = refactor.Refactor(self.project_root, filename)
        options = ref.get_refactor_options(offset)
        self.assertFalse(any(opt['name'] == "refactor_froms_to_imports"
                             for opt in options))
        filename, offset = self.create_file("foo.py",
                                            "imp_|_ort foo")
        ref = refactor.Refactor(self.project_root, filename)
        options = ref.get_refactor_options(offset)
        self.assertTrue(any(opt['name'] == "refactor_froms_to_imports"
                            for opt in options))


class TestGetChanges(RefactorTestCase):
    def test_should_fail_if_method_is_not_refactoring(self):
        filename, offset = self.create_file("foo.py")
        ref = refactor.Refactor(self.project_root, filename)
        self.assertRaises(ValueError, ref.get_changes, "bad_name")

    def test_should_return_method_results(self):
        filename, offset = self.create_file("foo.py")
        ref = refactor.Refactor(self.project_root, filename)
        with mock.patch.object(ref, 'refactor_extract_method') as test:
            test.return_value = "Meep!"
            self.assertEqual(ref.get_changes("refactor_extract_method",
                                             1, 2),
                             "Meep!")
            test.assert_called_with(1, 2)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestIsOnSymbol(RefactorTestCase):
    def test_should_find_symbol(self):
        filename, offset = self.create_file("test.py", "__B_|_AR = 100")
        r = refactor.Refactor(self.project_root, filename)
        self.assertTrue(r._is_on_symbol(offset))

    # Issue #111
    def test_should_find_symbol_with_underscores(self):
        filename, offset = self.create_file("test.py", "_|___BAR = 100")
        r = refactor.Refactor(self.project_root, filename)
        self.assertTrue(r._is_on_symbol(offset))

    def test_should_not_find_weird_places(self):
        filename, offset = self.create_file("test.py", "hello = _|_ 1 + 1")
        r = refactor.Refactor(self.project_root, filename)
        self.assertFalse(r._is_on_symbol(offset))


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestFromsToImports(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            """\
            _|_from datetime import datetime

            d = datetime(2013, 4, 7)
            """)
        ref = refactor.Refactor(self.project_root, filename)
        (change,) = ref.get_changes("refactor_froms_to_imports", offset)
        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], filename)
        self.assertSourceEqual(change['contents'],
                               """\
                               import datetime

                               d = datetime.datetime(2013, 4, 7)
                               """)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestOrganizeImports(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            """\
            import unittest, base64
            import datetime, json

            obj = json.dumps(23)
            unittest.TestCase()
            """)
        ref = refactor.Refactor(self.project_root, filename)
        (change,) = ref.get_changes("refactor_organize_imports")
        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], filename)
        self.assertSourceEqual(change['contents'],
                               """\
                               import json
                               import unittest


                               obj = json.dumps(23)
                               unittest.TestCase()
                               """)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestModuleToPackage(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            "_|_import os\n")
        ref = refactor.Refactor(self.project_root, filename)
        changes = ref.refactor_module_to_package()
        a, b, c = changes
        # Not sure why the a change is there. It's a CHANGE that
        # changes nothing...
        self.assertEqual(a['diff'], '')

        self.assertEqual(b['action'], 'create')
        self.assertEqual(b['type'], 'directory')
        self.assertEqual(b['path'], os.path.join(self.project_root, "foo"))

        self.assertEqual(c['action'], 'move')
        self.assertEqual(c['type'], 'file')
        self.assertEqual(c['source'], os.path.join(self.project_root,
                                                   "foo.py"))
        self.assertEqual(c['destination'], os.path.join(self.project_root,
                                                        "foo/__init__.py"))


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestRenameAtPoint(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            """\
            class Foo(object):
                def _|_foo(self):
                    return 5

                def bar(self):
                    return self.foo()
            """)
        file2, offset2 = self.create_file(
            "bar.py",
            """\
            import foo


            x = foo.Foo()
            x.foo()""")
        ref = refactor.Refactor(self.project_root, filename)
        first, second = ref.refactor_rename_at_point(offset, "frob",
                                                     in_hierarchy=False,
                                                     docs=False)
        if first['file'] == filename:
            a, b = first, second
        else:
            a, b = second, first
        self.assertEqual(a['action'], 'change')
        self.assertEqual(a['file'], filename)
        self.assertSourceEqual(a['contents'],
                               """\
                               class Foo(object):
                                   def frob(self):
                                       return 5

                                   def bar(self):
                                       return self.frob()
                               """)
        self.assertEqual(b['action'], 'change')
        self.assertEqual(b['file'], file2)
        self.assertSourceEqual(b['contents'],
                               """\
                               import foo


                               x = foo.Foo()
                               x.frob()""")

    def test_should_refactor_in_hierarchy(self):
        filename, offset = self.create_file(
            "foo.py",
            """\
            class Foo(object):
                def _|_foo(self):
                    return 5

                def bar(self):
                    return self.foo()

            class Bar(Foo):
                def foo(self):
                    return 42

            class Baz(object):
                def foo(self):
                    return 42
            """)
        file2, offset2 = self.create_file(
            "bar.py",
            """\
            import foo


            x, y, z = foo.Foo(), foo.Bar(), foo.Baz()
            x.foo()
            y.foo()
            z.foo()""")
        ref = refactor.Refactor(self.project_root, filename)
        first, second = ref.refactor_rename_at_point(offset, "frob",
                                                     in_hierarchy=True,
                                                     docs=False)
        if first['file'] == filename:
            a, b = first, second
        else:
            a, b = second, first
        self.assertEqual(a['action'], 'change')
        self.assertEqual(a['file'], filename)
        self.assertSourceEqual(a['contents'],
                               """\
                               class Foo(object):
                                   def frob(self):
                                       return 5

                                   def bar(self):
                                       return self.frob()

                               class Bar(Foo):
                                   def frob(self):
                                       return 42

                               class Baz(object):
                                   def foo(self):
                                       return 42
                               """)
        self.assertEqual(b['action'], 'change')
        self.assertEqual(b['file'], file2)
        self.assertSourceEqual(b['contents'],
                               """\
                               import foo


                               x, y, z = foo.Foo(), foo.Bar(), foo.Baz()
                               x.frob()
                               y.frob()
                               z.foo()""")

    def test_should_refactor_in_docstrings(self):
        filename, offset = self.create_file(
            "foo.py",
            """\
            class Foo(object):
                "Frobnicate the foo"
                def _|_foo(self):
                    return 5

            print("I'm an unrelated foo")
            """)
        ref = refactor.Refactor(self.project_root, filename)
        (change,) = ref.refactor_rename_at_point(offset, "frob",
                                                 in_hierarchy=False,
                                                 docs=True)
        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], filename)
        self.assertSourceEqual(change['contents'],
                               """\
                               class Foo(object):
                                   "Frobnicate the frob"
                                   def frob(self):
                                       return 5

                               print("I'm an unrelated foo")
                               """)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestRenameCurrentModule(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            "_|_import os\n")
        file2, offset = self.create_file(
            "bar.py",
            """\
            _|_import foo
            foo.os
            """)
        dest = os.path.join(self.project_root, "frob.py")
        ref = refactor.Refactor(self.project_root, filename)
        a, b = ref.refactor_rename_current_module("frob")

        self.assertEqual(a['action'], 'change')
        self.assertEqual(a['file'], file2)
        self.assertEqual(a['contents'],
                         "import frob\n"
                         "frob.os\n")

        self.assertEqual(b['action'], 'move')
        self.assertEqual(b['type'], 'file')
        self.assertEqual(b['source'], filename)
        self.assertEqual(b['destination'], dest)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestMoveModule(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            "_|_import os\n")
        file2, offset = self.create_file(
            "bar.py",
            """\
            _|_import foo
            foo.os
            """)
        dest = os.path.join(self.project_root, "frob")
        os.mkdir(dest)
        with open(os.path.join(dest, "__init__.py"), "w") as f:
            f.write("")
        ref = refactor.Refactor(self.project_root, filename)
        a, b = ref.refactor_move_module(dest)

        self.assertEqual(a['action'], 'change')
        self.assertEqual(a['file'], file2)
        self.assertSourceEqual(a['contents'],
                               """\
                               import frob.foo
                               frob.foo.os
                               """)

        self.assertEqual(b['action'], 'move')
        self.assertEqual(b['type'], 'file')
        self.assertEqual(b['source'], filename)
        self.assertEqual(b['destination'],
                         os.path.join(dest, "foo.py"))


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestCreateInline(RefactorTestCase):
    def setUp(self):
        super(TestCreateInline, self).setUp()
        self.filename, self.offset = self.create_file(
            "foo.py",
            """\
            def add(a, b):
                return a + b

            x = _|_add(2, 3)
            y = add(17, 4)
            """)

    def test_should_refactor_single_occurrenc(self):
        ref = refactor.Refactor(self.project_root, self.filename)
        (change,) = ref.refactor_create_inline(self.offset, True)

        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], self.filename)
        self.assertSourceEqual(change['contents'],
                               """\
                               def add(a, b):
                                   return a + b

                               x = 2 + 3
                               y = add(17, 4)
                               """)

    def test_should_refactor_all_occurrencs(self):
        ref = refactor.Refactor(self.project_root, self.filename)
        (change,) = ref.refactor_create_inline(self.offset, False)

        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], self.filename)
        self.assertSourceEqual(change['contents'],
                               """\
                               x = 2 + 3
                               y = 17 + 4
                               """)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestExtractMethod(RefactorTestCase):
    def setUp(self):
        super(TestExtractMethod, self).setUp()
        self.filename, self.offset = self.create_file(
            "foo.py",
            """\
            class Foo(object):
                def spaghetti(self, a, b):
                    _|_x = a + 5
                    y = b + 23
                    return y
            """)

    def test_should_refactor_local(self):
        ref = refactor.Refactor(self.project_root, self.filename)
        (change,) = ref.refactor_extract_method(self.offset, 104,
                                                "calc", False)
        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], self.filename)
        expected = """\
                   class Foo(object):
                       def spaghetti(self, a, b):
                           return self.calc(a, b)

                       def calc(self, a, b):
                           x = a + 5
                           y = b + 23
                           return y
                   """
        expected2 = expected.replace("return self.calc(a, b)",
                                     "return self.calc(b, a)")
        expected2 = expected2.replace("def calc(self, a, b)",
                                      "def calc(self, b, a)")
        # This is silly, but it's what we got.
        if change['contents'] == dedent(expected2):
            self.assertSourceEqual(change['contents'], expected2)
        else:
            self.assertSourceEqual(change['contents'], expected)

    def test_should_refactor_global(self):
        ref = refactor.Refactor(self.project_root, self.filename)
        (change,) = ref.refactor_extract_method(self.offset, 104,
                                                "calc", True)
        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], self.filename)
        expected = """\
                   class Foo(object):
                       def spaghetti(self, a, b):
                           return calc(a, b)

                   def calc(a, b):
                       x = a + 5
                       y = b + 23
                       return y
                   """
        expected2 = expected.replace("return calc(a, b)",
                                     "return calc(b, a)")
        expected2 = expected2.replace("def calc(a, b)",
                                      "def calc(b, a)")
        if change['contents'] == dedent(expected2):
            self.assertSourceEqual(change['contents'], expected2)
        else:
            self.assertSourceEqual(change['contents'], expected)


@unittest.skipIf(not refactor.ROPE_AVAILABLE, "Requires Rope")
class TestUseFunction(RefactorTestCase):
    def test_should_refactor(self):
        filename, offset = self.create_file(
            "foo.py",
            """\
            def _|_add_and_multiply(a, b, c):
                temp = a + b
                return temp * c

            f = 1 + 2
            g = f * 3
            """)

        ref = refactor.Refactor(self.project_root, filename)
        (change,) = ref.refactor_use_function(offset)

        self.assertEqual(change['action'], 'change')
        self.assertEqual(change['file'], filename)
        self.assertSourceEqual(change['contents'],
                               """\
                               def add_and_multiply(a, b, c):
                                   temp = a + b
                                   return temp * c

                               g = add_and_multiply(1, 2, 3)
                               """)

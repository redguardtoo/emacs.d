"""Tests for the elpy.jedibackend module."""

import unittest

import jedi
import mock

from elpy import jedibackend
from elpy import rpc
from elpy.tests import compat
from elpy.tests.support import BackendTestCase
from elpy.tests.support import RPCGetCompletionsTests
from elpy.tests.support import RPCGetCompletionDocstringTests
from elpy.tests.support import RPCGetCompletionLocationTests
from elpy.tests.support import RPCGetDocstringTests
from elpy.tests.support import RPCGetDefinitionTests
from elpy.tests.support import RPCGetCalltipTests
from elpy.tests.support import RPCGetUsagesTests


class JediBackendTestCase(BackendTestCase):
    def setUp(self):
        super(JediBackendTestCase, self).setUp()
        self.backend = jedibackend.JediBackend(self.project_root)


class TestInit(JediBackendTestCase):
    def test_should_have_jedi_as_name(self):
        self.assertEqual(self.backend.name, "jedi")


class TestRPCGetCompletions(RPCGetCompletionsTests,
                            JediBackendTestCase):
    pass


class TestRPCGetCompletionDocstring(RPCGetCompletionDocstringTests,
                                    JediBackendTestCase):
    pass


class TestRPCGetCompletionLocation(RPCGetCompletionLocationTests,
                                   JediBackendTestCase):
    pass


class TestRPCGetDocstring(RPCGetDocstringTests,
                          JediBackendTestCase):
    THREAD_JOIN_DOCSTRING = 'join(self, timeout = None)'


class TestRPCGetDefinition(RPCGetDefinitionTests,
                           JediBackendTestCase):
    pass


class TestRPCGetCalltip(RPCGetCalltipTests,
                        JediBackendTestCase):
    KEYS_CALLTIP = {'index': 0,
                    'params': [''],
                    'name': u'keys'}
    RADIX_CALLTIP = {'index': None,
                     'params': [],
                     'name': u'radix'}
    ADD_CALLTIP = {'index': 0,
                   'params': [u'a', u'b'],
                   'name': u'add'}
    if compat.PYTHON3:
        THREAD_CALLTIP = {"name": "Thread",
                          "params": ["group = None",
                                     "target = None",
                                     "name = None",
                                     "args = ()",
                                     "kwargs = None",
                                     "daemon = None"],
                          "index": 0}
    else:
        THREAD_CALLTIP = {"name": "Thread",
                          "params": ["group = None",
                                     "target = None",
                                     "name = None",
                                     "args = ()",
                                     "kwargs = None",
                                     "verbose = None"],
                          "index": 0}


class TestRPCGetUsages(RPCGetUsagesTests,
                       JediBackendTestCase):
    def test_should_not_fail_for_missing_module(self):
        # This causes use.module_path to be None
        source = "import sys\n\nsys.path.\n"  # insert()"
        offset = 21
        filename = self.project_file("project.py", source)

        self.rpc(filename, source, offset)


class TestPosToLinecol(unittest.TestCase):
    def test_should_handle_beginning_of_string(self):
        self.assertEqual(jedibackend.pos_to_linecol("foo", 0),
                         (1, 0))

    def test_should_handle_end_of_line(self):
        self.assertEqual(jedibackend.pos_to_linecol("foo\nbar\nbaz\nqux", 9),
                         (3, 1))

    def test_should_handle_end_of_string(self):
        self.assertEqual(jedibackend.pos_to_linecol("foo\nbar\nbaz\nqux", 14),
                         (4, 2))


class TestLinecolToPos(unittest.TestCase):
    def test_should_handle_beginning_of_string(self):
        self.assertEqual(jedibackend.linecol_to_pos("foo", 1, 0),
                         0)

    def test_should_handle_end_of_string(self):
        self.assertEqual(jedibackend.linecol_to_pos("foo\nbar\nbaz\nqux",
                                                    3, 1),
                         9)

    def test_should_return_offset(self):
        self.assertEqual(jedibackend.linecol_to_pos("foo\nbar\nbaz\nqux",
                                                    4, 2),
                         14)

    def test_should_fail_for_line_past_text(self):
        self.assertRaises(ValueError,
                          jedibackend.linecol_to_pos, "foo\n", 3, 1)

    def test_should_fail_for_column_past_text(self):
        self.assertRaises(ValueError,
                          jedibackend.linecol_to_pos, "foo\n", 1, 10)


class TestRunWithDebug(unittest.TestCase):
    @mock.patch('jedi.Script')
    def test_should_call_method(self, Script):
        Script.return_value.test_method.return_value = "test-result"

        result = jedibackend.run_with_debug(jedi, 'test_method', 1, 2, arg=3)

        Script.assert_called_with(1, 2, arg=3)
        self.assertEqual(result, 'test-result')

    @mock.patch('jedi.Script')
    def test_should_re_raise(self, Script):
        Script.side_effect = RuntimeError

        with self.assertRaises(RuntimeError):
            jedibackend.run_with_debug(jedi, 'test_method', 1, 2, arg=3,
                                       re_raise=(RuntimeError,))

    @mock.patch('jedi.Script')
    @mock.patch('jedi.set_debug_function')
    def test_should_keep_debug_info(self, set_debug_function, Script):
        Script.side_effect = RuntimeError

        try:
            jedibackend.run_with_debug(jedi, 'test_method', 1, 2, arg=3)
        except rpc.Fault as e:
            self.assertGreaterEqual(e.code, 400)
            self.assertIsNotNone(e.data)
            self.assertIn("traceback", e.data)
            jedi_debug_info = e.data["jedi_debug_info"]
            self.assertIsNotNone(jedi_debug_info)
            self.assertEqual(jedi_debug_info["script_args"],
                             "1, 2, arg=3")
            self.assertEqual(jedi_debug_info["source"], None)
            self.assertEqual(jedi_debug_info["method"], "test_method")
            self.assertEqual(jedi_debug_info["debug_info"], [])
        else:
            self.fail("Fault not thrown")

    @mock.patch('jedi.Script')
    @mock.patch('jedi.set_debug_function')
    def test_should_keep_error_text(self, set_debug_function, Script):
        Script.side_effect = RuntimeError

        try:
            jedibackend.run_with_debug(jedi, 'test_method', 1, 2, arg=3)
        except rpc.Fault as e:
            self.assertEqual(str(e), str(RuntimeError()))
            self.assertEqual(e.message, str(RuntimeError()))
        else:
            self.fail("Fault not thrown")

    @mock.patch('jedi.Script')
    @mock.patch('jedi.set_debug_function')
    def test_should_handle_source_special(self, set_debug_function, Script):
        Script.side_effect = RuntimeError

        try:
            jedibackend.run_with_debug(jedi, 'test_method', source="foo")
        except rpc.Fault as e:
            self.assertEqual(e.data["jedi_debug_info"]["script_args"],
                             "source=source")
            self.assertEqual(e.data["jedi_debug_info"]["source"], "foo")
        else:
            self.fail("Fault not thrown")

    @mock.patch('jedi.Script')
    @mock.patch('jedi.set_debug_function')
    def test_should_set_debug_info(self, set_debug_function, Script):
        the_debug_function = [None]

        def my_set_debug_function(debug_function, **kwargs):
            the_debug_function[0] = debug_function

        def my_script(*args, **kwargs):
            the_debug_function[0](jedi.debug.NOTICE, "Notice")
            the_debug_function[0](jedi.debug.WARNING, "Warning")
            the_debug_function[0]("other", "Other")
            raise RuntimeError

        set_debug_function.side_effect = my_set_debug_function
        Script.return_value.test_method = my_script

        try:
            jedibackend.run_with_debug(jedi, 'test_method', source="foo")
        except rpc.Fault as e:
            self.assertEqual(e.data["jedi_debug_info"]["debug_info"],
                             ["[N] Notice",
                              "[W] Warning",
                              "[?] Other"])
        else:
            self.fail("Fault not thrown")

    @mock.patch('jedi.set_debug_function')
    @mock.patch('jedi.Script')
    def test_should_not_fail_with_bad_data(self, Script, set_debug_function):
        import jedi.debug

        def set_debug(function, speed=True):
            if function is not None:
                function(jedi.debug.NOTICE, u"\xab")

        set_debug_function.side_effect = set_debug
        Script.return_value.test_method.side_effect = Exception

        with self.assertRaises(rpc.Fault):
            jedibackend.run_with_debug(jedi, 'test_method', 1, 2, arg=3)

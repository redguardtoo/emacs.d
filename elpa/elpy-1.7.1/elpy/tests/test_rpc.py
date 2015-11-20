"""Tests for elpy.rpc."""

import json
import unittest
import sys

from elpy import rpc
from elpy.tests.compat import StringIO


class TestFault(unittest.TestCase):
    def test_should_have_code_and_data(self):
        fault = rpc.Fault("Hello", code=250, data="Fnord")
        self.assertEqual(str(fault), "Hello")
        self.assertEqual(fault.code, 250)
        self.assertEqual(fault.data, "Fnord")

    def test_should_have_defaults_for_code_and_data(self):
        fault = rpc.Fault("Hello")
        self.assertEqual(str(fault), "Hello")
        self.assertEqual(fault.code, 500)
        self.assertIsNone(fault.data)


class TestJSONRPCServer(unittest.TestCase):
    def setUp(self):
        self.stdin = StringIO()
        self.stdout = StringIO()
        self.rpc = rpc.JSONRPCServer(self.stdin, self.stdout)

    def write(self, s):
        self.stdin.seek(0)
        self.stdin.truncate()
        self.stdout.seek(0)
        self.stdout.truncate()
        self.stdin.write(s)
        self.stdin.seek(0)

    def read(self):
        value = self.stdout.getvalue()
        self.stdin.seek(0)
        self.stdin.truncate()
        self.stdout.seek(0)
        self.stdout.truncate()
        return value


class TestInit(TestJSONRPCServer):
    def test_should_use_arguments(self):
        self.assertEqual(self.rpc.stdin, self.stdin)
        self.assertEqual(self.rpc.stdout, self.stdout)

    def test_should_default_to_sys(self):
        testrpc = rpc.JSONRPCServer()
        self.assertEqual(sys.stdin, testrpc.stdin)
        self.assertEqual(sys.stdout, testrpc.stdout)


class TestReadJson(TestJSONRPCServer):
    def test_should_read_json(self):
        objlist = [{'foo': 'bar'},
                   {'baz': 'qux', 'fnord': 'argl\nbargl'},
                   "beep\r\nbeep\r\nbeep"]
        self.write("".join([(json.dumps(obj) + "\n")
                            for obj in objlist]))
        for obj in objlist:
            self.assertEqual(self.rpc.read_json(),
                             obj)

    def test_should_raise_eof_on_eof(self):
        self.assertRaises(EOFError, self.rpc.read_json)

    def test_should_fail_on_malformed_json(self):
        self.write("malformed json\n")
        self.assertRaises(ValueError,
                          self.rpc.read_json)


class TestWriteJson(TestJSONRPCServer):
    def test_should_write_json_line(self):
        objlist = [{'foo': 'bar'},
                   {'baz': 'qux', 'fnord': 'argl\nbargl'},
                   ]
        for obj in objlist:
            self.rpc.write_json(**obj)
            self.assertEqual(json.loads(self.read()),
                             obj)


class TestHandleRequest(TestJSONRPCServer):
    def test_should_fail_if_json_does_not_contain_a_method(self):
        self.write(json.dumps(dict(params=[],
                                   id=23)))
        self.assertRaises(ValueError,
                          self.rpc.handle_request)

    def test_should_call_right_method(self):
        self.write(json.dumps(dict(method='foo',
                                   params=[1, 2, 3],
                                   id=23)))
        self.rpc.rpc_foo = lambda *params: params
        self.rpc.handle_request()
        self.assertEqual(json.loads(self.read()),
                         dict(id=23,
                              result=[1, 2, 3]))

    def test_should_pass_defaults_for_missing_parameters(self):
        def test_method(*params):
            self.args = params

        self.write(json.dumps(dict(method='foo')))
        self.rpc.rpc_foo = test_method
        self.rpc.handle_request()
        self.assertEqual(self.args, ())
        self.assertEqual(self.read(), "")

    def test_should_return_error_for_missing_method(self):
        self.write(json.dumps(dict(method='foo',
                                   id=23)))
        self.rpc.handle_request()
        result = json.loads(self.read())

        self.assertEqual(result["id"], 23)
        self.assertEqual(result["error"]["message"],
                         "Unknown method foo")

    def test_should_return_error_for_exception_in_method(self):
        def test_method():
            raise ValueError("An error was raised")

        self.write(json.dumps(dict(method='foo',
                                   id=23)))
        self.rpc.rpc_foo = test_method

        self.rpc.handle_request()
        result = json.loads(self.read())

        self.assertEqual(result["id"], 23)
        self.assertEqual(result["error"]["message"], "An error was raised")
        self.assertIn("traceback", result["error"]["data"])

    def test_should_not_include_traceback_for_faults(self):
        def test_method():
            raise rpc.Fault("This is a fault")

        self.write(json.dumps(dict(method="foo",
                                   id=23)))
        self.rpc.rpc_foo = test_method

        self.rpc.handle_request()
        result = json.loads(self.read())

        self.assertEqual(result["id"], 23)
        self.assertEqual(result["error"]["message"], "This is a fault")
        self.assertNotIn("traceback", result["error"])

    def test_should_add_data_for_faults(self):
        def test_method():
            raise rpc.Fault("St. Andreas' Fault",
                            code=12345, data="Yippieh")

        self.write(json.dumps(dict(method="foo", id=23)))
        self.rpc.rpc_foo = test_method

        self.rpc.handle_request()
        result = json.loads(self.read())

        self.assertEqual(result["error"]["data"], "Yippieh")

    def test_should_call_handle_for_unknown_method(self):
        def test_handle(method_name, args):
            return "It works"
        self.write(json.dumps(dict(method="doesnotexist",
                                   id=23)))
        self.rpc.handle = test_handle
        self.rpc.handle_request()
        self.assertEqual(json.loads(self.read()),
                         dict(id=23,
                              result="It works"))


class TestServeForever(TestJSONRPCServer):
    def handle_request(self):
        self.hr_called += 1
        if self.hr_called > 10:
            raise self.error()

    def setUp(self):
        super(TestServeForever, self).setUp()
        self.hr_called = 0
        self.error = KeyboardInterrupt
        self.rpc.handle_request = self.handle_request

    def test_should_call_handle_request_repeatedly(self):
        self.rpc.serve_forever()
        self.assertEqual(self.hr_called, 11)

    def test_should_return_on_some_errors(self):
        self.error = KeyboardInterrupt
        self.rpc.serve_forever()
        self.error = EOFError
        self.rpc.serve_forever()
        self.error = SystemExit
        self.rpc.serve_forever()

    def test_should_fail_on_most_errors(self):
        self.error = RuntimeError
        self.assertRaises(RuntimeError,
                          self.rpc.serve_forever)

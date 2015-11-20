"""
    anaconda_mode
    ~~~~~~~~~~~~~

    This is anaconda_mode autocompletion server.

    :copyright: (c) 2013-2015 by Artem Malyshev.
    :license: GPL3, see LICENSE for more details.
"""

from __future__ import (
    absolute_import, unicode_literals, division, print_function)

import sys
from functools import wraps
from os.path import abspath, dirname
from pkg_resources import get_distribution, DistributionNotFound
from subprocess import Popen

project_path = dirname(abspath(__file__))

sys.path.insert(0, project_path)

missing_dependencies = []

try:
    from jedi import Script, NotFoundError
except ImportError:
    missing_dependencies.append('jedi')

try:
    from service_factory import service_factory
except ImportError:
    missing_dependencies.append('service_factory')

if missing_dependencies:
    command = ['pip', 'install', '-t', project_path] + missing_dependencies
    pip = Popen(command)
    pip.communicate()
    assert pip.returncode is 0, 'PyPi installation fails.'
    from jedi import Script, NotFoundError
    from service_factory import service_factory

print('Python executable:', sys.executable)
for package in ['jedi', 'service_factory']:
    try:
        version = get_distribution(package).version
    except DistributionNotFound:
        print('Unable to find {package} version'.format(package=package))
    else:
        print('{package} version: {version}'.format(
            package=package, version=version))


def script_method(f):
    """Create jedi.Script instance and apply f to it."""

    @wraps(f)
    def wrapper(source, line, column, path):
        try:
            return f(Script(source, line, column, path))
        except NotFoundError:
            return []

    return wrapper


@script_method
def complete(script):
    """Select auto-complete candidates for source position."""

    def first_line(text):
        """Return text first line."""
        return text.strip().split('\n', 1)[0]

    return [{'name': comp.name,
             'doc': comp.docstring() or None,
             'info': first_line(comp.docstring(raw=True)) or None,
             'type': comp.type,
             'path': comp.module_path or None,
             'line': comp.line}
            for comp in script.completions()]


@script_method
def doc(script):
    """Documentation for all definitions at point."""
    docs = ['\n'.join([d.module_name + ' - ' + d.description,
                       '=' * 40,
                       d.docstring() or "- No docstring -"]).strip()
            for d in script.goto_definitions()]

    return ('\n' + '-' * 40 + '\n').join(docs)


def process_definitions(f):

    @wraps(f)
    def wrapper(script):
        cache = {script.path: script.source.splitlines()}

        def get_description(d):
            if d.module_path not in cache:
                with open(d.module_path, 'r') as file:
                    cache[d.module_path] = file.read().splitlines()

            return cache[d.module_path][d.line - 1]

        return [{'line': d.line,
                 'column': d.column,
                 'name': d.name,
                 'description': get_description(d),
                 'module': d.module_name,
                 'type': d.type,
                 'path': d.module_path}
                for d in f(script) if not d.in_builtin_module()]

    return wrapper


@script_method
@process_definitions
def goto_definitions(script):
    return script.goto_definitions()


@script_method
@process_definitions
def goto_assignments(script):
    return script.goto_assignments()


@script_method
@process_definitions
def usages(script):
    return script.usages()


@script_method
def eldoc(script):
    """Return eldoc format documentation string or ''."""
    signatures = script.call_signatures()

    if len(signatures) == 1:
        sgn = signatures[0]
        return {
            'name': sgn.name,
            'index': sgn.index,
            'params': [p.description for p in sgn.params]
        }

    return {}


app = [complete, doc, goto_definitions, goto_assignments, usages, eldoc]


if __name__ == '__main__':
    host = sys.argv[1] if len(sys.argv) == 2 else '127.0.0.1'
    service_factory(app, host, 'auto', 'anaconda_mode port {port}')

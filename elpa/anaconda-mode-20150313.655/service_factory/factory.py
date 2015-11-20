"""
    service_factory.factory
    ~~~~~~~~~~~~~~~~~~~~~~~

    This module define service factory.

    :copyright: (c) 2015 by Artem Malyshev.
    :license: GPL3, see LICENSE for more details.
"""

from __future__ import (
    absolute_import, unicode_literals, division, print_function)

from .providers.basehttp import HTTPServiceProvider
from .service import Service


def service_factory(app, host, port,
                    report_message='service factory port {port}',
                    provider_cls=HTTPServiceProvider):
    """Create service, start server.

    :param app: application to instantiate a service
    :param host: interface to bound provider
    :param port: port to bound provider
    :param report_message: message format to report port
    :param provider_cls: server class provide a service

    """

    service = Service(app)
    server = provider_cls(service, host, port, report_message)
    server.serve_forever()

import pytest
from pybitwuzla import Bitwuzla, Option, Kind, Result

@pytest.fixture
def solver():
    return Bitwuzla()

def test_new():
    Bitwuzla()



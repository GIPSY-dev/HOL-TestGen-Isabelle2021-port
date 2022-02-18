
port=8080

# server home directory
server =.

fcc=fsharpc --nologo
cc=gmcs

deploy: bin/HealthCareService.dll

run: deploy
	xsp --port $(port)

bar: bin/bar.exe
	mono bin/bar.exe

init: bin/init.exe
	mono bin/init.exe

include server.mk

clean:
	rm bin/* gen/* lib/* -rf

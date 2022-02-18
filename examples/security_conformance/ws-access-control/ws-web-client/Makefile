
port=8080
# server home directory

server=../ws-server
include $(server)/server.mk

fPort=8081

fcc=fsharpc --nologo
cc=gmcs

deploy: $(server)/lib/HealthCareStubs.dll bin/logic.dll

#bin/Main.dll

run: deploy
	xsp --port $(fPort)

clean:
	rm bin/* -rf

bin/logic.dll: logic.fs
	$(fcc) -a $^ /r:$(server)/lib/HealthCareStubs.dll -o $@

bin/HealthCareStubs.dll: $(server)/lib/HealthCareStubs.dll
	cp $^ $@

#bin/Main.dll: main.cs bin/logic.dll
#	$(cc) /out:$@ /r:System.dll,$(server)/lib/HealthCareStubs.dll,bin/logic.dll,System.Web.dll,System.Data.dll /t:library main.cs


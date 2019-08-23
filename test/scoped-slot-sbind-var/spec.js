it('scoped slot mixed var- and s-bind, by given content', function (done) {
    const clickInfo = {}
    // [inject] init

    expect(wrap.getElementsByTagName('h3')[0].innerHTML).toBe('errorrik')
    expect(wrap.getElementsByTagName('b')[0].innerHTML).toBe('male')
    expect(wrap.getElementsByTagName('u')[0].innerHTML).toBe('errorrik@gmail.com')
    myComponent.data.set('man.email', 'erik168@163.com')
    myComponent.data.set('man.name', 'erik')
    san.nextTick(function () {
        expect(wrap.getElementsByTagName('h3')[0].innerHTML).toBe('erik')
        expect(wrap.getElementsByTagName('b')[0].innerHTML).toBe('male')
        expect(wrap.getElementsByTagName('u')[0].innerHTML).toBe('erik168@163.com')

        triggerEvent(wrap.getElementsByTagName('u')[0], 'click')
        setTimeout(function () {
            expect(clickInfo.email).toBe('erik168@163.com')
            expect(clickInfo.outer).toBeTruthy()

            myComponent.dispose()
            document.body.removeChild(wrap)
            done()
        }, 500)
    })
})

it('date data', function (done) {
    // [inject] init

    const b = wrap.getElementsByTagName('b')[0]

    expect(b.title).toBe('1983')

    myComponent.data.set('date', new Date(myComponent.data.get('date').getFullYear() + 1, 10, 10))

    san.nextTick(function () {
        const b = wrap.getElementsByTagName('b')[0]

        expect(b.title).toBe('1984')

        myComponent.dispose()
        document.body.removeChild(wrap)
        done()
    })
})
